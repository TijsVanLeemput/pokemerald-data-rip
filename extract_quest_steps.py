#!/usr/bin/env python3
"""
Generate a human-readable walkthrough for every quest, straight from the ROM.

Usage:
    python3 extract_quest_steps.py [input/game.gba] [-o output/quest_steps.md] [--quest N]

Writes output/quest_steps.md (walkthrough) and output/quest_steps.csv (one row per step).

How it works
  * Every map event script (NPCs, signs, step triggers, map scripts) is run
    symbolically: each possible path through the script is followed, with the
    conditions taken on the way (flag set?, var == n?, answered Yes?, has item?,
    is it night?, which menu option?) and what the path does (dialogue, battles,
    items/Pokemon given or taken, flags/vars changed, quest started/completed).
  * For each quest, the paths that start or complete it give its "state": the
    flags and vars they change. Every other path that changes that state is a
    step of the quest.
  * Steps are ordered by dependency (a step that sets var = 2 comes before a
    step that needs var == 2, a step that gives an item before one that needs it).
  * Quests that run along the main story also list the story events between their
    start and completion (the story variable is detected automatically).
  * Conditions and actions are turned into sentences; items you must bring are
    looked up in output/items.csv, Pokemon in output/encounters.csv.

Run extract_items.py and extract_encounters.py first for the "where to find"
lines. Needs extract_encounters.py, extract_items.py and extract_quests.py.
"""
import argparse, csv, os, re, struct, sys
from collections import defaultdict, Counter, OrderedDict, namedtuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from extract_encounters import (Rom, ROM_BASE, TEXT_END, MAP_HEADER_REGION_MAP_SECTION, POINTER_SIZE,
                                POINTER_ALIGNMENT_MASK, U16_SIZE, POKEMON_NAME_LENGTH, find_species, find_map_groups,
                                find_region_map_entries, mapsec_names)
from extract_items import (CMD_LEN, END_CMDS, CREATEMON, ScriptCmd, STD_OBTAIN_ITEM, STD_FIND_ITEM, VARS_START,
                           SPECIAL_VARS_START, SPECIAL_VARS_END, VAR_ITEM_ID, VAR_ITEM_AMOUNT, MAX_SCRIPT_DISTANCE,
                           CALLNATIVE_SIZE, TRAINERBATTLE_TRAINER, TRAINERBATTLE_CONTINUE_SCRIPT, SIDE_PLAYER,
                           OBJECT_EVENT_GRAPHICS_ID, OBJECT_EVENT_FLAG, COORD_EVENT_VAR, COORD_EVENT_VALUE,
                           MAP_SCRIPT_ON_FRAME_TABLE, MAP_SCRIPT_ON_WARP_INTO_MAP_TABLE, command_args,
                           find_items, iter_maps, iter_map_scripts, iter_map_script_table, collect_entries,
                           learn_native_args, cmd_len, native_len)
from extract_quests import (decode, find_quest_table, SIDE_QUEST_SIZE, SIDE_QUEST_NAME, SIDE_QUEST_DESCRIPTION,
                            SIDE_QUEST_DONE_DESCRIPTION, SIDE_QUEST_MAP, EXPANSION_GFX_NAMES, OBJ_EVENT_MON,
                            OBJ_EVENT_MON_FLAGS, QUEST_CASE_UNLOCK, QUEST_CASE_START, QUEST_CASE_REWARD,
                            QUEST_CASE_COMPLETE, QUEST_CASE_CHECK_UNLOCKED, QUEST_CASE_CHECK_COMPLETE)

# --- limits of the symbolic execution and the step analysis
MAX_PATHS = 250              # per script
MAX_STEPS = 4000             # instructions per path
MAX_POSITION_FORKS = 2       # branches on the player's position followed both ways per path
DEFAULT_BULK = 15            # paths that change more flags/vars than this are new-game setup, not quest steps
MAX_FLAG_USERS = 8           # a flag used by more scripts than this is too general to be quest state
MAX_VAR_USERS = 15           # same for vars
MIN_STORY_VALUES = 15        # the story variable is the var set to at least this many different values
MAX_DEPENDENCY_ROUNDS = 6    # rounds of "add the steps that unlock a step already in the quest"
MIN_FINAL_STEP_CONDITIONS = 3   # a quest giver's path needs this many conditions to count as "after completion"
STORY_ACTION_WEIGHT = 3      # picking a story path: one action counts as much as this many lines of dialogue
MAX_STORY_PATHS = 2          # story paths shown per story value
MAX_DIALOGUE_LENGTH = 4000   # bytes read per message

# --- output
MAX_LISTED_MAPS = 3          # maps listed in "Talk to ... at A / B / C"
MIN_QUOTE_LENGTH = 12        # shorter dialogue lines aren't quoted
MAX_RECEIPT_LENGTH = 90      # "You received X!" lines longer than this are quoted, not turned into "Receive X"
RECEIVE_PREFIX = "Receive "
MAX_SEPARATE_QUEST_PREREQUISITES = 3   # more "after finishing quest N" conditions than this are merged into one
MAX_ITEM_LOCATIONS = 4       # "Where to find" entries per item
MAX_CATCH_LOCATIONS = 3      # "Where to catch" entries per species
FINISHED_QUEST_RE = re.compile(r"^after finishing quest (?P<number>\d+) ")

# --- game constants
TEMP_VARS_COUNT = 0x10       # VAR_TEMP_0 .. VAR_TEMP_F, cleared on every map load
SCRATCH_VARS_END = 0x4020    # temp vars followed by VAR_OBJ_GFX_ID_0 .. F
TEMP_FLAGS_END = 0x20        # flags 0x00-0x1F are temporary (cleared on every map load)
TEMP_VARS = set(range(VARS_START, VARS_START + TEMP_VARS_COUNT)) | set(range(SPECIAL_VARS_START, SPECIAL_VARS_END))
TEMP_FLAGS = set(range(0, TEMP_FLAGS_END))
VAR_RESULT, VAR_8000 = 0x800D, 0x8000   # VAR_RESULT; VAR_0x8000 (e.g. the time-of-day native writes here)
VAR_INITIAL_VALUE = 0        # every var starts out as 0
U16_MAX = 0xFFFF
TRUE, FALSE = 1, 0           # result of yes/no boxes, checkitem, quest checks, ...
FLAG_SET = 1                 # checkflag's comparison result when the flag is set
STD_MSGBOX_NPC, STD_MSGBOX_SIGN, STD_MSGBOX_DEFAULT, STD_MSGBOX_YESNO, STD_MSGBOX_AUTOCLOSE = 2, 3, 4, 5, 6
MSGBOX = {STD_MSGBOX_NPC, STD_MSGBOX_SIGN, STD_MSGBOX_DEFAULT, STD_MSGBOX_YESNO, STD_MSGBOX_AUTOCLOSE}
MSGBOX_TEXT_SLOT = 0         # msgbox = loadword 0, text; callstd MSGBOX_*
TRAINER_NAME_MAX_BYTES = 13  # trainer names are read up to this many bytes
MIN_TRAINER_STRIDE, MAX_TRAINER_STRIDE = 16, 256   # sizes of struct Trainer tried
MIN_TRAINER_VOTES = 3        # pairs of speaker names that must agree on the gTrainers layout
MAX_NAME_MATCHES = 40        # ROM matches of one speaker name considered
# gMultichoiceLists: {const struct MenuAction *list; u8 count; 3 bytes padding}
MULTICHOICE_LIST_SIZE = 8
MULTICHOICE_LIST_ACTIONS, MULTICHOICE_LIST_COUNT = 0, 4
MENU_ACTION_SIZE = 8         # struct MenuAction { const u8 *text; void (*func)(); }
MENU_ACTION_TEXT = 0
MAX_MULTICHOICE_OPTIONS = 20
MAX_MENU_TEXT_LENGTH = 60
MIN_MULTICHOICE_LISTS = 64
# expansion natives recognised by their inline arguments (bytes after callnative)
SPECIES_NATIVE_ARGS = U16_SIZE        # checkspecies-style: species
DEX_NATIVE_ARGS = 2 * U16_SIZE        # species, caught (else seen)
OBJECT_XY_NATIVE_ARGS = 4 * U16_SIZE  # getobjectxy: localId, useTemplate, x var, y var
TIMES = ["in the morning", "during the day", "in the evening", "at night"]
# comparison operators of goto_if / call_if (pokeemerald: LT, EQ, GT, LE, GE, NE)
CMP_LT, CMP_EQ, CMP_GT, CMP_LE, CMP_GE, CMP_NE = range(6)
COND_FN = {CMP_LT: lambda left, right: left < right, CMP_EQ: lambda left, right: left == right,
           CMP_GT: lambda left, right: left > right, CMP_LE: lambda left, right: left <= right,
           CMP_GE: lambda left, right: left >= right, CMP_NE: lambda left, right: left != right}
COND_TXT = {CMP_LT: "<", CMP_EQ: "==", CMP_GT: ">", CMP_LE: "<=", CMP_GE: ">=", CMP_NE: "!="}
NEGATED_CMP = {CMP_LT: CMP_GE, CMP_EQ: CMP_NE, CMP_GT: CMP_LE, CMP_LE: CMP_GT, CMP_GE: CMP_LT, CMP_NE: CMP_EQ}
QUEST_CASE_VERBS = {QUEST_CASE_UNLOCK: "Unlocks", QUEST_CASE_START: "Starts", QUEST_CASE_REWARD: "Readies",
                    QUEST_CASE_COMPLETE: "Completes"}
# order of the groups of steps in a walkthrough
GROUP_BEFORE_START, GROUP_START, GROUP_MIDDLE, GROUP_COMPLETE, GROUP_AFTERWARDS = range(5)

# --- what a script path does (Path.effects); the first field is always the kind
Dialogue = namedtuple("Dialogue", "kind speaker text")            # say, phone
ItemChange = namedtuple("ItemChange", "kind item amount")         # give_item, find_item, take_item
VarChange = namedtuple("VarChange", "kind var value")             # setvar (value), addvar (value = delta)
FlagChange = namedtuple("FlagChange", "kind flag value")          # flag (value True = set)
SpecialCall = namedtuple("SpecialCall", "kind special")
Warp = namedtuple("Warp", "kind map")                             # map: MapId
TrainerBattle = namedtuple("TrainerBattle", "kind trainer speaker")
PokemonEvent = namedtuple("PokemonEvent", "kind species level")   # give_mon, wild (battle)
EggGift = namedtuple("EggGift", "kind species")
Shop = namedtuple("Shop", "kind")
MoneyChange = namedtuple("MoneyChange", "kind amount")
QuestChange = namedtuple("QuestChange", "kind case quest")
MapId = namedtuple("MapId", "group num")
# --- conditions a path took (Path.conds)
VarCondition = namedtuple("VarCondition", "kind var comparison value source")   # source: what last set the var
FlagCondition = namedtuple("FlagCondition", "kind flag value")                  # flag: id or TrainerFlag
TrainerFlag = namedtuple("TrainerFlag", "kind trainer")
# --- the pending comparison (Path.cmp)
VarComparison = namedtuple("VarComparison", "kind var value")
VarVarComparison = namedtuple("VarVarComparison", "kind var other_var")
FlagComparison = namedtuple("FlagComparison", "kind flag")
# --- where a result variable's value came from (Path.src, VarCondition.source)
ResultSource = namedtuple("ResultSource", "kind")                # yesno, position, time
SpecialResult = namedtuple("SpecialResult", "kind special")
MenuResult = namedtuple("MenuResult", "kind menu")
HasItemResult = namedtuple("HasItemResult", "kind item amount")
MoneyResult = namedtuple("MoneyResult", "kind amount")
SpeciesResult = namedtuple("SpeciesResult", "kind species")
DexResult = namedtuple("DexResult", "kind species caught")
QuestCheckResult = namedtuple("QuestCheckResult", "kind case quest")
YESNO_RESULT, POSITION_RESULT, TIME_RESULT = ResultSource("yesno"), ResultSource("position"), ResultSource("time")
# --- what a step provides / requires (orders the steps)
FlagState = namedtuple("FlagState", "kind flag value")
ItemHeld = namedtuple("ItemHeld", "kind item")
VarValue = namedtuple("VarValue", "kind var value")
VarRequirement = namedtuple("VarRequirement", "kind var comparison value")
# --- where a script is attached (Analysis.where)
ScriptLocation = namedtuple("ScriptLocation", "map x y kind event_offset")
StoryCandidate = namedtuple("StoryCandidate", "score script path")
GENERIC_SPRITES = {"BOY", "GIRL", "LITTLE_BOY", "LITTLE_GIRL", "RICH_BOY", "WOMAN", "FAT_MAN", "POKEFAN",
                   "MAN", "EXPERT", "COOK", "OLD_MAN", "OLD_WOMAN", "CAMPER", "PICNICKER", "YOUNGSTER",
                   "BUG_CATCHER", "PSYCHIC", "SCHOOL_KID", "MANIAC", "HEX_MANIAC", "SWIMMER", "BLACK_BELT",
                   "BEAUTY", "SCIENTIST", "LASS", "GENTLEMAN", "SAILOR", "FISHERMAN", "RUNNING_TRIATHLETE",
                   "TUBER", "HIKER", "CYCLING_TRIATHLETE", "NURSE", "REPORTER", "BARD", "ARTIST", "CAMERAMAN",
                   "TWIN", "NINJA_BOY", "MART_EMPLOYEE", "LINK_RECEPTIONIST", "GAMEBOY_KID", "TUBER_M_SWIMMING",
                   "DEVON_EMPLOYEE", "MOM", "QUINTY_PLUMP"}
RECEIPT_RE = re.compile(r"^(?:\(?)(?:You(?:'ve| have)? (?:just )?(?:earned|received|obtained)|Obtained|You registered)"
                        r"\s+(?:the |a |an )?(?P<what>.+?)[.!)]*$")


# ------------------------------------------------------------------ helpers --
def clean_text(text):
    text = re.sub(r"(?:… ?)+", " ", text)
    text = re.sub(r"\s*\.\.\.\s*\.\.\.\s*", "... ", text)
    return re.sub(r"\s{2,}", " ", text).strip()


def shorten(text, max_length=None):
    """Clean up dialogue for output. Text is never cut unless max_length is given."""
    text = clean_text(text)
    if max_length is None or len(text) <= max_length: return text
    head = text[:max_length]
    return (head[:head.rfind(" ")] if " " in head else head) + "…"   # cut at the last whole word


def find_multichoice_table(rom):
    """gMultichoiceLists: the first run of at least MIN_MULTICHOICE_LISTS plausible list entries."""
    def is_list_entry(offset):
        list_pointer = rom.u32(offset + MULTICHOICE_LIST_ACTIONS)
        option_count = rom.data[offset + MULTICHOICE_LIST_COUNT]
        padding = rom.data[offset + MULTICHOICE_LIST_COUNT + 1:offset + MULTICHOICE_LIST_SIZE]
        if (not rom.isptr(list_pointer) or list_pointer & POINTER_ALIGNMENT_MASK
                or not (1 <= option_count <= MAX_MULTICHOICE_OPTIONS) or any(padding)):
            return False
        list_offset = rom.off(list_pointer)
        for i in range(option_count):
            text_pointer = rom.u32(list_offset + MENU_ACTION_SIZE * i + MENU_ACTION_TEXT)
            if not rom.isptr(text_pointer): return False
            if TEXT_END not in rom.data[rom.off(text_pointer):rom.off(text_pointer) + MAX_MENU_TEXT_LENGTH]: return False
        return True
    offset, scan_end = 0, rom.size - MULTICHOICE_LIST_SIZE * MIN_MULTICHOICE_LISTS
    while offset < scan_end:
        if is_list_entry(offset):
            entry_count = 0
            while is_list_entry(offset + MULTICHOICE_LIST_SIZE * entry_count): entry_count += 1
            if entry_count >= MIN_MULTICHOICE_LISTS: return offset
            offset += MULTICHOICE_LIST_SIZE * max(entry_count, 1)
        else:
            offset += POINTER_SIZE
    return None


def find_trainer_names(rom, pairs):
    """pairs: [(trainerId, speakerName)]. Trainer names are stored inline in gTrainers;
    find (base, stride) that puts several known speaker names at their trainer ids."""
    from extract_encounters import CHARMAP
    inv = {char: code for code, char in CHARMAP.items() if len(char) == 1}
    occ = {}
    for tid, name in set(pairs):
        try: enc = bytes(inv[char] for char in name) + bytes([TEXT_END])
        except KeyError: continue
        occ[(tid, name)] = [match.start() for match in re.finditer(re.escape(enc), rom.data)][:MAX_NAME_MATCHES]
    votes = Counter()
    keys = list(occ.items())
    for i in range(len(keys)):
        for j in range(i + 1, len(keys)):
            (first_trainer, _), first_offsets = keys[i]
            (second_trainer, _), second_offsets = keys[j]
            if first_trainer == second_trainer: continue
            for first_offset in first_offsets:
                for second_offset in second_offsets:
                    if (second_offset - first_offset) % (second_trainer - first_trainer): continue
                    stride_candidate = (second_offset - first_offset) // (second_trainer - first_trainer)
                    if MIN_TRAINER_STRIDE <= stride_candidate <= MAX_TRAINER_STRIDE:
                        votes[(first_offset - first_trainer * stride_candidate, stride_candidate)] += 1
    if not votes: return None
    base, stride = max(votes, key=votes.get)
    if votes[(base, stride)] < MIN_TRAINER_VOTES: return None
    return lambda trainer_id: (rom.text(base + stride * trainer_id, TRAINER_NAME_MAX_BYTES)
                               if 0 <= base + stride * trainer_id < rom.size else "")


def range_tiles(tiles):
    """[(x, y)] -> '9,13-15' style text."""
    tiles = sorted(set(tiles))
    first_x, first_y = tiles[0]
    if len(tiles) == 1: return "%s,%s" % (first_x, first_y)
    x_values, y_values = {x for x, y in tiles}, {y for x, y in tiles}
    if len(x_values) == 1: return "%s,%s–%s" % (first_x, min(y_values), max(y_values))
    if len(y_values) == 1: return "%s–%s,%s" % (min(x_values), max(x_values), first_y)
    return "%s,%s (+%d tiles)" % (first_x, first_y, len(tiles) - 1)


# ---------------------------------------------------------- symbolic paths --
class Path:
    __slots__ = ("pc", "stack", "env", "cons", "flags", "src", "cmp", "conds", "effects", "speaker",
                 "regs", "seen", "steps", "end", "last_speaker", "pos_forks")

    def fork(self):
        clone = Path.__new__(Path)
        clone.pc, clone.stack, clone.env, clone.flags = self.pc, list(self.stack), dict(self.env), dict(self.flags)
        clone.cons = {var_id: list(constraints) for var_id, constraints in self.cons.items()}
        clone.src, clone.cmp, clone.conds, clone.effects = dict(self.src), self.cmp, list(self.conds), list(self.effects)
        clone.speaker, clone.regs, clone.seen, clone.steps, clone.end = self.speaker, dict(self.regs), set(self.seen), self.steps, self.end
        clone.last_speaker, clone.pos_forks = self.last_speaker, self.pos_forks
        return clone


def object_xy_result_vars(rom, pc):
    """The vars a getobjectxy-style callnative at pc writes the x and y position to."""
    local_id, use_template, x_var, y_var = struct.unpack_from("<HHHH", rom.data, pc + CALLNATIVE_SIZE)
    return x_var, y_var


def feasible(cons):
    cands = {0, 1, U16_MAX}
    for comparison_op, value in cons:
        cands |= {value - 1, value, value + 1}
    return any(all(COND_FN[comparison_op](candidate, value) for comparison_op, value in cons) for candidate in cands if 0 <= candidate <= U16_MAX)


class Machine:
    def __init__(self, rom, natives, ctx):
        self.rom, self.natives, self.ctx = rom, natives, ctx

    def run(self, start, entry_cond=None):
        path = Path()
        path.pc, path.stack, path.env, path.cons, path.flags, path.src = start, [], {}, {}, {}, {}
        path.cmp, path.conds, path.effects, path.speaker, path.regs, path.seen, path.steps, path.end = None, [], [], None, {}, set(), 0, None
        path.last_speaker, path.pos_forks = None, 0
        if entry_cond:
            var_id, val = entry_cond
            path.env[var_id] = val; path.cons[var_id] = [(CMP_EQ, val)]
            path.conds.append(VarCondition("var", var_id, CMP_EQ, val, None))
        todo, done = [path], []
        while todo and len(done) < MAX_PATHS:
            path = todo.pop()
            while path.end is None:
                if path.steps > MAX_STEPS or not (0 <= path.pc < self.rom.size):
                    path.end = "limit"; break
                key = (path.pc, tuple(path.stack))
                if key in path.seen:
                    path.end = "loop"; break
                path.seen.add(key); path.steps += 1
                fork = self.step(path)
                if fork is not None: todo.append(fork)
            done.append(path)
        return done

    # ---- helpers
    def set_var(self, path, var_id, val):
        path.env[var_id] = val; path.cons.pop(var_id, None); path.src.pop(var_id, None)

    def new_result(self, path, var, desc):
        path.env.pop(var, None); path.cons.pop(var, None); path.src[var] = desc

    def branch(self, path, cond, target, is_call):
        """returns fork (or None); p continues with the not-taken side."""
        comparison = path.cmp
        outcome = None
        if comparison and comparison.kind == "var" and comparison.var in path.env:
            outcome = COND_FN[cond](path.env[comparison.var], comparison.value)
        elif comparison and comparison.kind == "varvar" and comparison.var in path.env and comparison.other_var in path.env:
            outcome = COND_FN[cond](path.env[comparison.var], path.env[comparison.other_var])
        elif comparison and comparison.kind == "flag" and comparison.flag in path.flags:
            flag_value = FLAG_SET if path.flags[comparison.flag] else 0
            outcome = COND_FN[cond](flag_value, FLAG_SET)
        if outcome is not None:
            if outcome: self.jump(path, target, is_call)
            return None
        # branches on the player's position only pick a walking route. Follow both sides for the
        # first MAX_POSITION_FORKS of them in a path, after that only the jump (avoids 2^n identical paths)
        if (comparison and comparison.kind == "varvar") or \
                (comparison and comparison.kind == "var" and path.src.get(comparison.var) == POSITION_RESULT):
            path.pos_forks += 1
            if path.pos_forks > MAX_POSITION_FORKS:
                self.jump(path, target, is_call); return None
            taken = path.fork(); self.jump(taken, target, is_call)
            return taken
        taken = path.fork()
        ok_t = self.assume(taken, cond, True)
        ok_n = self.assume(path, cond, False)
        if ok_t: self.jump(taken, target, is_call)
        if not ok_n:
            if ok_t:   # only the taken side is possible: continue with it
                return self._replace(path, taken)
            path.end = "infeasible"
        return taken if ok_t else None

    def _replace(self, path, source):
        for slot in Path.__slots__: setattr(path, slot, getattr(source, slot))
        return None

    def assume(self, path, cond, truth):
        comparison = path.cmp
        if comparison is None: return True
        if comparison.kind == "flag":
            # checkflag: comparison result FLAG_SET when set; == / >= FLAG_SET -> set, < / != FLAG_SET -> clear
            want = {CMP_EQ: True, CMP_GE: True, CMP_LT: False, CMP_NE: False}.get(cond)
            if want is None: return truth if cond == CMP_LE else not truth if cond == CMP_GT else True
            val = want if truth else not want
            if comparison.flag in path.flags and path.flags[comparison.flag] != val: return False
            path.flags[comparison.flag] = val
            path.conds.append(FlagCondition("flag", comparison.flag, val))
            return True
        if comparison.kind == "var":
            var_id, val = comparison.var, comparison.value
            comparison_op = cond if truth else NEGATED_CMP[cond]
            cons = path.cons.setdefault(var_id, []) + [(comparison_op, val)]
            if not feasible(cons): return False
            path.cons[var_id] = cons
            if comparison_op == CMP_EQ: path.env[var_id] = val
            path.conds.append(VarCondition("var", var_id, comparison_op, val, path.src.get(var_id)))
            return True
        return True   # var-vs-var (positions): no constraint

    def jump(self, path, target, is_call):
        if not self.rom.isptr(target):
            path.end = "badptr"; return
        if is_call: path.stack.append(path.pc)
        path.pc = self.rom.off(target)

    def say(self, path, text_ptr, kind="say"):
        if self.rom.isptr(text_ptr):
            text = decode(self.rom, self.rom.off(text_ptr), maxlen=MAX_DIALOGUE_LENGTH)
            if "{STR_VAR_1}' is now {STR_VAR_2}" in text: return     # startquest/completequest banner
            path.effects.append(Dialogue(kind, path.speaker, text))

    # ---- one instruction; p.pc is advanced (or jumped). Returns a forked path or None.
    def step(self, path):
        rom, pc, game = self.rom, path.pc, self.ctx
        opcode = rom.data[pc]
        length = cmd_len(rom, pc, self.natives)
        if not length:
            path.end = "unknown op 0x%02X" % opcode; return None
        args = lambda fmt: command_args(rom, pc, fmt)    # the command's own arguments
        native_args = lambda fmt: struct.unpack_from("<" + fmt, rom.data, pc + CALLNATIVE_SIZE)   # after a callnative
        path.pc = pc + length
        if opcode == ScriptCmd.END:
            path.end = "end"
        elif opcode == ScriptCmd.RETURN:
            if path.stack: path.pc = path.stack.pop()
            else: path.end = "end"
        elif opcode in (ScriptCmd.CALL, ScriptCmd.GOTO):
            target, = args("I")
            self.jump(path, target, opcode == ScriptCmd.CALL)
        elif opcode in (ScriptCmd.GOTO_IF, ScriptCmd.CALL_IF):
            cond, target = args("BI")
            return self.branch(path, cond, target, opcode == ScriptCmd.CALL_IF)
        elif opcode == ScriptCmd.LOADWORD:
            slot, value = args("BI")
            if slot == MSGBOX_TEXT_SLOT: path.regs["text"] = value
        elif opcode in (ScriptCmd.GOTOSTD, ScriptCmd.CALLSTD):
            std, = args("B")
            if std in MSGBOX and "text" in path.regs:
                text_pointer = path.regs.pop("text")
                self.say(path, text_pointer)
                if std == STD_MSGBOX_YESNO:
                    self.new_result(path, VAR_RESULT, YESNO_RESULT)
            elif std in (STD_OBTAIN_ITEM, STD_FIND_ITEM) and VAR_ITEM_ID in path.regs:
                item, qty = path.regs[VAR_ITEM_ID], path.regs.get(VAR_ITEM_AMOUNT, 1)
                if item < VARS_START:
                    path.effects.append(ItemChange("give_item" if std == STD_OBTAIN_ITEM else "find_item", item,
                                                   qty if qty < VARS_START else 1))
                self.new_result(path, VAR_RESULT, None)
            if opcode == ScriptCmd.GOTOSTD: path.end = "end"
        elif opcode == ScriptCmd.MESSAGE:
            text_pointer, = args("I")
            self.say(path, text_pointer)
        elif opcode == ScriptCmd.SETSPEAKERNAME:
            name_pointer, = args("I")
            path.speaker = decode(rom, rom.off(name_pointer)) if rom.isptr(name_pointer) else None
            if path.speaker and path.speaker != "???": path.last_speaker = path.speaker
        elif opcode == ScriptCmd.CLEARSPEAKERNAME: path.speaker = None
        elif opcode == ScriptCmd.POKENAVCALL:
            text_pointer, = args("I")
            self.say(path, text_pointer, "phone")
        elif opcode in (ScriptCmd.SETVAR, ScriptCmd.SETORCOPYVAR):
            var_id, val = args("HH")
            if opcode == ScriptCmd.SETORCOPYVAR and val >= VARS_START:
                if val in path.env: self.set_var(path, var_id, path.env[val])
                else: path.env.pop(var_id, None); path.cons.pop(var_id, None)
                if val in path.src: path.src[var_id] = path.src[val]
            else:
                self.set_var(path, var_id, val)
                if var_id in (VAR_ITEM_ID, VAR_ITEM_AMOUNT): path.regs[var_id] = val
                if var_id not in TEMP_VARS: path.effects.append(VarChange("setvar", var_id, val))
        elif opcode in (ScriptCmd.ADDVAR, ScriptCmd.SUBVAR):
            var_id, val = args("HH")
            delta = val if opcode == ScriptCmd.ADDVAR else -val
            if var_id in path.env:
                self.set_var(path, var_id, (path.env[var_id] + delta) & U16_MAX)
            else:
                path.cons.pop(var_id, None)
            if var_id not in TEMP_VARS: path.effects.append(VarChange("addvar", var_id, delta))
        elif opcode == ScriptCmd.COPYVAR:
            dest_var, source_var = args("HH")
            if source_var in path.env: self.set_var(path, dest_var, path.env[source_var])
            else: path.env.pop(dest_var, None); path.cons[dest_var] = list(path.cons.get(source_var, []))
            if source_var in path.src: path.src[dest_var] = path.src[source_var]
            else: path.src.pop(dest_var, None)
        elif opcode == ScriptCmd.COMPARE_VAR_TO_VALUE: path.cmp = VarComparison("var", *args("HH"))
        elif opcode == ScriptCmd.COMPARE_VAR_TO_VAR: path.cmp = VarVarComparison("varvar", *args("HH"))
        elif opcode == ScriptCmd.CHECKFLAG: path.cmp = FlagComparison("flag", *args("H"))
        elif opcode in (ScriptCmd.SETFLAG, ScriptCmd.CLEARFLAG):
            flag_id, = args("H")
            path.flags[flag_id] = opcode == ScriptCmd.SETFLAG
            if flag_id not in TEMP_FLAGS: path.effects.append(FlagChange("flag", flag_id, opcode == ScriptCmd.SETFLAG))
        elif opcode == ScriptCmd.CHECKTRAINERFLAG:
            trainer_id, = args("H")
            path.cmp = FlagComparison("flag", TrainerFlag("trainer", trainer_id))
        elif opcode == ScriptCmd.SPECIAL: path.effects.append(SpecialCall("special", *args("H")))
        elif opcode == ScriptCmd.SPECIALVAR:
            result_var, special = args("HH")
            self.new_result(path, result_var, SpecialResult("special", special))
        elif opcode in (ScriptCmd.WARP, ScriptCmd.WARPSILENT, ScriptCmd.WARPDOOR, ScriptCmd.WARPHOLE, ScriptCmd.WARPTELEPORT):
            path.effects.append(Warp("warp", MapId(*args("BB"))))
        elif opcode == ScriptCmd.GETPLAYERXY:
            for position_var in args("HH"): self.new_result(path, position_var, POSITION_RESULT)
        elif opcode == ScriptCmd.ADDITEM:
            path.effects.append(ItemChange("give_item", *args("HH"))); self.new_result(path, VAR_RESULT, None)
        elif opcode == ScriptCmd.REMOVEITEM: path.effects.append(ItemChange("take_item", *args("HH")))
        elif opcode == ScriptCmd.CHECKITEM: self.new_result(path, VAR_RESULT, HasItemResult("has_item", *args("HH")))
        elif opcode == ScriptCmd.TRAINERBATTLE:
            trainer_id = rom.u16(pc + TRAINERBATTLE_TRAINER)
            path.effects.append(TrainerBattle("trainer", trainer_id, path.speaker or path.last_speaker))
            continue_script = rom.u32(pc + TRAINERBATTLE_CONTINUE_SCRIPT)
            if rom.isptr(continue_script) and abs(rom.off(continue_script) - pc) < MAX_SCRIPT_DISTANCE:
                self.jump(path, continue_script, False)
        elif opcode == ScriptCmd.YESNOBOX: self.new_result(path, VAR_RESULT, YESNO_RESULT)
        elif opcode in (ScriptCmd.MULTICHOICE, ScriptCmd.MULTICHOICEDEFAULT, ScriptCmd.MULTICHOICEGRID):
            left, top, menu_id = args("BBB")
            self.new_result(path, VAR_RESULT, MenuResult("menu", menu_id))
        elif opcode == ScriptCmd.GIVEMON:
            path.effects.append(PokemonEvent("give_mon", *args("HB"))); self.new_result(path, VAR_RESULT, None)
        elif opcode == ScriptCmd.GIVEEGG: path.effects.append(EggGift("give_egg", *args("H")))
        elif opcode == ScriptCmd.POKEMART: path.effects.append(Shop("shop"))
        elif opcode in (ScriptCmd.ADDMONEY, ScriptCmd.REMOVEMONEY):
            amount, = args("I")
            path.effects.append(MoneyChange("money", amount if opcode == ScriptCmd.ADDMONEY else -amount))
        elif opcode == ScriptCmd.CHECKMONEY: self.new_result(path, VAR_RESULT, MoneyResult("money", *args("I")))
        elif opcode == ScriptCmd.SETWILDBATTLE: path.effects.append(PokemonEvent("wild", *args("HB")))
        elif opcode == ScriptCmd.QUESTMENU:
            case, quest_id = args("BB")
            if QUEST_CASE_UNLOCK <= case <= QUEST_CASE_COMPLETE:
                path.effects.append(QuestChange("quest", case, quest_id))
            elif QUEST_CASE_CHECK_UNLOCKED <= case <= QUEST_CASE_CHECK_COMPLETE:
                self.new_result(path, VAR_RESULT, QuestCheckResult("questcheck", case, quest_id))
        elif opcode == ScriptCmd.CALLNATIVE:
            target, = args("I")
            kind = game.native_kind.get(target)
            if self.natives.get(target) == CREATEMON:
                side, slot, species, level = native_args("BBHH")
                if side == SIDE_PLAYER: path.effects.append(PokemonEvent("give_mon", species, level))
                self.new_result(path, VAR_RESULT, None)
            elif kind == "time": self.new_result(path, VAR_8000, TIME_RESULT)
            elif kind == "species": self.new_result(path, VAR_RESULT, SpeciesResult("species", *native_args("H")))
            elif kind == "dex": self.new_result(path, VAR_RESULT, DexResult("dex", *native_args("HH")))
            elif kind == "objxy":
                for position_var in object_xy_result_vars(rom, pc): self.new_result(path, position_var, POSITION_RESULT)
        return None


# ------------------------------------------------------------- the game --
class Game:
    def __init__(self, rom, here):
        self.rom = rom
        species_base, sst, sno, _, self.scount = find_species(rom)
        self.species = lambda species_id: (rom.text(species_base + sst * species_id + sno, POKEMON_NAME_LENGTH + 1)
                                           if 0 < species_id < self.scount else "species #%d" % species_id)
        _, _, _, self.item = find_items(rom)
        self.quest_table, self.quest_count = find_quest_table(rom)
        self.qnames = [decode(rom, rom.off(rom.u32(self.quest_table + SIDE_QUEST_SIZE * i + SIDE_QUEST_NAME)))
                       for i in range(self.quest_count)]
        map_groups, _ = find_map_groups(rom)
        rme = find_region_map_entries(rom)
        secs = mapsec_names(rom, rme) if rme is not None else []
        self.maps = list(iter_maps(rom, map_groups))
        self.mapname_ = {}
        for map_group, map_num, map_header in self.maps:
            sec = rom.data[map_header + MAP_HEADER_REGION_MAP_SECTION]
            self.mapname_[(map_group, map_num)] = "%s (%d.%d)" % (secs[sec] if sec < len(secs) else "MAPSEC_%d" % sec, map_group, map_num)
        self.entries, _, _ = collect_entries(rom, self.maps)
        self.natives = learn_native_args(rom, sorted({entry.script for entry in self.entries}))
        self.native_kind = self.classify_natives()
        self.multichoice_table = find_multichoice_table(rom)
        self.items_csv = self.load_csv(os.path.join(here, "output", "items.csv"))
        self.enc_csv = self.load_csv(os.path.join(here, "output", "encounters.csv"))

    def menu(self, menu_id, option):
        """Text of an option of a multichoice menu."""
        rom, table = self.rom, self.multichoice_table
        if table is None: return "option %d" % (option + 1)
        list_entry = table + MULTICHOICE_LIST_SIZE * menu_id
        if option >= rom.data[list_entry + MULTICHOICE_LIST_COUNT]: return "option %d" % (option + 1)
        actions = rom.off(rom.u32(list_entry + MULTICHOICE_LIST_ACTIONS))
        return decode(rom, rom.off(rom.u32(actions + MENU_ACTION_SIZE * option + MENU_ACTION_TEXT)))

    def mapname(self, map_ref):
        """map_ref: anything with .group and .num (MapRef, MapId)."""
        return self.mapname_.get((map_ref.group, map_ref.num), "map %d.%d" % (map_ref.group, map_ref.num))

    @staticmethod
    def load_csv(path):
        if not os.path.exists(path): return []
        with open(path, encoding="utf-8") as csv_file: return list(csv.DictReader(csv_file))

    def classify_natives(self):
        """Recognise a few expansion natives by how scripts use them."""
        from extract_items import Walker
        rom, votes = self.rom, defaultdict(Counter)
        walker = Walker(rom, self.natives)
        for script in sorted({entry.script for entry in self.entries}):
            for pc in walker.walk(script).visited:
                if rom.data[pc] != ScriptCmd.CALLNATIVE: continue
                target, = command_args(rom, pc, "I")
                arg_bytes = native_len(rom, pc, self.natives)
                native_species = lambda: rom.u16(pc + CALLNATIVE_SIZE)               # first inline argument
                native_caught = lambda: rom.u16(pc + CALLNATIVE_SIZE + U16_SIZE)     # second one (dex natives)
                next_pc = pc + CALLNATIVE_SIZE + arg_bytes
                compared_var = compared_value = None   # a compare_var_to_value right after the native
                if rom.data[next_pc] == ScriptCmd.COMPARE_VAR_TO_VALUE:
                    compared_var, compared_value = command_args(rom, next_pc, "HH")
                if arg_bytes == 0 and compared_var == VAR_8000 and compared_value < len(TIMES):
                    votes[target]["time"] += 1
                elif arg_bytes == SPECIES_NATIVE_ARGS and compared_var == VAR_RESULT and 0 < native_species() < self.scount:
                    votes[target]["species"] += 1
                elif arg_bytes == DEX_NATIVE_ARGS and compared_var == VAR_RESULT and 0 < native_species() < self.scount \
                        and native_caught() in (FALSE, TRUE):
                    votes[target]["dex"] += 1
                elif arg_bytes == OBJECT_XY_NATIVE_ARGS and all(VARS_START <= result_var < SCRATCH_VARS_END
                                                                for result_var in object_xy_result_vars(rom, pc)):
                    votes[target]["objxy"] += 1
                else: votes[target]["other"] += 1
        out = {}
        for target, kind_counts in votes.items():
            kind = max(kind_counts, key=kind_counts.get)
            classified_votes = sum(kind_counts.values()) - kind_counts["other"]
            if kind != "other" and kind_counts[kind] > classified_votes / 2 \
                    and (kind != "objxy" or kind_counts["other"] == 0):
                out[target] = kind
        return out


def entry_conditions(rom, entries):
    """Triggers and frame/warp-into map scripts only run when var == value."""
    out = {}
    for entry in entries:
        if entry.kind == "trigger":
            var_id = rom.u16(entry.event_offset + COORD_EVENT_VAR)
            val = rom.u16(entry.event_offset + COORD_EVENT_VALUE)
            if var_id: out.setdefault(entry.script, (var_id, val))
    seen = set()
    for entry in entries:
        map_header = entry.map.header
        if entry.kind != "mapscript" or map_header in seen: continue
        seen.add(map_header)
        for script_type, table in iter_map_scripts(rom, map_header):
            if script_type in (MAP_SCRIPT_ON_FRAME_TABLE, MAP_SCRIPT_ON_WARP_INTO_MAP_TABLE):
                for var_id, val, script in iter_map_script_table(rom, table):
                    out.setdefault(script, (var_id, val))
    return out


# ------------------------------------------------------------- analysis --
class Analysis:
    def __init__(self, game, bulk=DEFAULT_BULK, max_flag_users=MAX_FLAG_USERS, max_var_users=MAX_VAR_USERS):
        self.game, self.bulk = game, bulk
        self.machine = Machine(game.rom, game.natives, game)
        self.where = defaultdict(list)
        for entry in game.entries:
            self.where[entry.script].append(ScriptLocation(entry.map, entry.x, entry.y, entry.kind, entry.event_offset))
        self.entry_cond = entry_conditions(game.rom, game.entries)
        self.paths = {}
        for script in self.where:
            self.paths[script] = self.machine.run(script, self.entry_cond.get(script))
        # who reads / writes what
        self.writers_f, self.writers_v = defaultdict(set), defaultdict(set)
        self.users_f, self.users_v = defaultdict(set), defaultdict(set)
        for script, paths in self.paths.items():
            for path in paths:
                for effect in path.effects:
                    if effect.kind == "flag": self.writers_f[effect.flag].add(script); self.users_f[effect.flag].add(script)
                    elif effect.kind in ("setvar", "addvar"): self.writers_v[effect.var].add(script); self.users_v[effect.var].add(script)
                for path_condition in path.conds:
                    if path_condition.kind == "flag" and not isinstance(path_condition.flag, TrainerFlag):
                        self.users_f[path_condition.flag].add(script)
                    elif path_condition.kind == "var": self.users_v[path_condition.var].add(script)
        self.max_flag_users, self.max_var_users = max_flag_users, max_var_users
        self.story_var = self.find_story_var()
        self.trainer_name = find_trainer_names(game.rom, [(effect.trainer, effect.speaker)
                                                         for paths in self.paths.values() for path in paths
                                                         for effect in path.effects if effect.kind == "trainer" and effect.speaker])
        self.story_paths = defaultdict(list)
        if self.story_var is not None:
            for script, paths in self.paths.items():
                for path in paths:
                    story_value = self.final_value(path, self.story_var)
                    if story_value is not None: self.story_paths[story_value].append((script, path))
        # quest completion / story milestones that set a flag or var (for "after ..." conditions)
        self.flag_from_quest, self.var_from_quest = {}, {}
        for script, paths in self.paths.items():
            for path in paths:
                done = [effect.quest for effect in path.effects if effect.kind == "quest" and effect.case == QUEST_CASE_COMPLETE]
                for quest_id in done:
                    for effect in path.effects:
                        if effect.kind == "flag" and effect.value: self.flag_from_quest.setdefault(effect.flag, quest_id)
                        if effect.kind == "setvar": self.var_from_quest.setdefault((effect.var, effect.value), quest_id)

    # ---- small queries
    def final_value(self, path, var):
        val = None
        for effect in path.effects:
            if effect.kind == "setvar" and effect.var == var: val = effect.value
        return val

    def path_writes(self, path):
        return {("f", effect.flag) for effect in path.effects if effect.kind == "flag"} | \
               {("v", effect.var) for effect in path.effects if effect.kind in ("setvar", "addvar")}

    def is_bulk(self, path):
        return len(self.path_writes(path)) > self.bulk

    def find_story_var(self):
        vals = defaultdict(set)
        for paths in self.paths.values():
            for path in paths:
                for effect in path.effects:
                    if effect.kind == "setvar" and effect.var not in TEMP_VARS: vals[effect.var].add(effect.value)
        if not vals: return None
        var_id = max(vals, key=lambda var: len(vals[var]))
        return var_id if len(vals[var_id]) >= MIN_STORY_VALUES else None

    def quest_paths_all(self, quest_id):
        """every path of every script that starts or completes quest q"""
        scripts = {script for script, paths in self.paths.items() for path in paths
                   if any(effect.kind == "quest" and effect.quest == quest_id for effect in path.effects)}
        return [path for script in scripts for path in self.paths[script]]

    def quest_paths(self, quest_id, case):
        return [(script, path) for script, paths in self.paths.items() for path in paths
                if any(effect.kind == "quest" and effect.case == case and effect.quest == quest_id for effect in path.effects)]

    # ---- the steps of one quest
    def quest_steps(self, quest_id):
        starts = self.quest_paths(quest_id, QUEST_CASE_START) + self.quest_paths(quest_id, QUEST_CASE_UNLOCK)
        dones = self.quest_paths(quest_id, QUEST_CASE_COMPLETE)
        core = starts + dones
        state_f, state_v = set(), set()
        for script, path in core:
            if self.is_bulk(path): continue
            for effect in path.effects:
                if effect.kind == "flag" and len(self.users_f[effect.flag]) <= self.max_flag_users: state_f.add(effect.flag)
                if effect.kind in ("setvar", "addvar") and effect.var != self.story_var and \
                        len(self.users_v[effect.var]) <= self.max_var_users: state_v.add(effect.var)
            for path_condition in path.conds:
                if path_condition.kind == "var" and path_condition.var not in TEMP_VARS and path_condition.var != self.story_var and \
                        len(self.users_v[path_condition.var]) <= self.max_var_users: state_v.add(path_condition.var)
                if path_condition.kind == "flag" and not isinstance(path_condition.flag, TrainerFlag) and \
                        path_condition.flag not in TEMP_FLAGS and \
                        len(self.users_f[path_condition.flag]) <= self.max_flag_users: state_f.add(path_condition.flag)
        # NPCs that start/complete the quest: their visibility flags
        npc_flags = set()
        for script, path in core:
            for location in self.where[script]:
                if location.kind != "object": continue
                visibility_flag = self.game.rom.u16(location.event_offset + OBJECT_EVENT_FLAG)
                if visibility_flag not in TEMP_FLAGS: npc_flags.add(visibility_flag)
        steps = []
        seen_paths = set()
        def add(script, path, role):
            if id(path) in seen_paths: return None
            seen_paths.add(id(path)); step = Step(self, quest_id, script, path, role, state_f, state_v); steps.append(step)
            return step
        for script, path in starts: add(script, path, "start")
        for script, path in dones: add(script, path, "done")
        # other paths that change the quest state in a way some quest step is waiting for
        cands = []
        for script, paths in self.paths.items():
            for path in paths:
                if id(path) in seen_paths or self.is_bulk(path): continue
                writes = self.path_writes(path)
                if any(write_kind == "f" and flag_id in state_f for write_kind, flag_id in writes) or \
                        any(write_kind == "v" and var_id in state_v for write_kind, var_id in writes):
                    cands.append((script, path, Step(self, quest_id, script, path, "step", state_f, state_v)))
                elif any(effect.kind == "flag" and not effect.value and effect.flag in npc_flags
                         and self.only_hidden_by_setup(effect.flag, core, path) for effect in path.effects):
                    add(script, path, "unlock")
        if not dones:
            # nothing completes the quest: show what the quest giver does once you're done
            for script in {script for script, path in starts}:
                for path in self.paths[script]:
                    if id(path) not in seen_paths and not self.is_bulk(path) and \
                            any(effect.kind in ("setvar", "special") and (effect.kind != "setvar" or effect.var not in TEMP_VARS)
                                for effect in path.effects) and len(path.conds) >= MIN_FINAL_STEP_CONDITIONS:
                        add(script, path, "final")
        for _ in range(MAX_DEPENDENCY_ROUNDS):
            reqs = [requirement for step in steps for requirement in step.requires]
            added = False
            for script, path, step in cands:
                if id(path) in seen_paths: continue
                if any(satisfies(provided, requirement) for provided in step.provides for requirement in reqs):
                    seen_paths.add(id(path)); steps.append(step); added = True
            if not added: break
        # story events between start and completion
        story_var = self.story_var
        if story_var is not None:
            start_story_values = [self.final_value(path, story_var) for script, path in starts if self.final_value(path, story_var) is not None]
            done_story_values = [self.final_value(path, story_var) for script, path in dones if self.final_value(path, story_var) is not None]
            if start_story_values and done_story_values:
                # every story value strictly between the start and the completion
                for story_value in range(max(start_story_values) + 1, min(done_story_values)):
                    for script, path in self.pick_story(story_value):
                        if id(path) not in seen_paths:
                            seen_paths.add(id(path)); steps.append(Step(self, quest_id, script, path, "story", state_f, state_v, story=story_value))
        if story_var is not None and start_story_values and done_story_values:
            story_low, story_high = max(start_story_values), min(done_story_values)
            keep = []
            for step in steps:
                pos = step.story_pos()
                if step.role in ("step",) and pos is not None and not (story_low <= pos <= story_high): continue
                keep.append(step)
            steps = keep
        return order_steps(self, steps, state_v)

    def story_pos(self, path):
        if self.story_var is None: return None
        story_value = self.final_value(path, self.story_var)
        if story_value is not None: return story_value
        need = None
        for path_condition in path.conds:
            if path_condition.kind == "var" and path_condition.var == self.story_var \
                    and path_condition.comparison in (CMP_EQ, CMP_GT, CMP_GE):
                # story > n means at least n + 1
                required_value = path_condition.value + (1 if path_condition.comparison == CMP_GT else 0)
                need = required_value if need is None else max(need, required_value)
        return need

    def only_hidden_by_setup(self, flag_id, core, clearer):
        """Is clearing flag f a real 'unlock'? Only if everything else that hides the NPC is
        new-game setup or happens earlier in the story than the clearing."""
        own = {script for script, path in core}
        cpos = self.story_pos(clearer)
        for script, paths in self.paths.items():
            if script in own: continue
            for path in paths:
                if not self.is_bulk(path) and any(effect.kind == "flag" and effect.flag == flag_id and effect.value
                                                  for effect in path.effects):
                    spos = self.story_pos(path)
                    if cpos is None: return False
                    if spos is not None and spos >= cpos: return False   # (setters we can't place are ignored)
        return True

    def pick_story(self, story_value):
        """The most informative path(s) that move the story to v (one per distinct event)."""
        cands = self.story_paths.get(story_value, [])
        best = {}   # script -> StoryCandidate
        for script, path in cands:
            if self.is_bulk(path) and not any(effect.kind == "quest" for effect in path.effects):
                continue
            actions = sum(1 for effect in path.effects if effect.kind != "say")
            dialogue = sum(1 for effect in path.effects if effect.kind == "say")
            score = actions * STORY_ACTION_WEIGHT + dialogue
            if script not in best or score > best[script].score: best[script] = StoryCandidate(score, script, path)
        if not best:
            return list(cands[:1])   # nothing informative: fall back to the first path
        # several scripts can set the same value (e.g. two trigger rows): keep the best one per map
        per_map = {}
        for candidate in best.values():
            first_location = self.where[candidate.script][0]
            if first_location.map not in per_map or candidate.score > per_map[first_location.map].score:
                per_map[first_location.map] = candidate
        ranked = sorted(per_map.values(), key=lambda candidate: -candidate.score)
        return [(candidate.script, candidate.path) for candidate in ranked][:MAX_STORY_PATHS]


# ---------------------------------------------------------------- steps --
class Step:
    def __init__(self, analysis, quest_id, script, path, role, state_f, state_v, story=None):
        self.analysis, self.quest_id, self.script, self.path, self.role = analysis, quest_id, script, path, role
        self.state_f, self.state_v, self.story = state_f, state_v, story
        game = analysis.game
        self.provides, self.requires = set(), []
        for effect in path.effects:
            if effect.kind == "flag": self.provides.add(FlagState("flag", effect.flag, effect.value))
            if effect.kind in ("give_item", "find_item"): self.provides.add(ItemHeld("item", effect.item))
        for var_id in state_v:
            val = analysis.final_value(path, var_id)
            if val is not None: self.provides.add(VarValue("var", var_id, val))
        for location in analysis.where[script]:
            if location.kind == "object":
                visibility_flag = game.rom.u16(location.event_offset + OBJECT_EVENT_FLAG)
                if visibility_flag and visibility_flag not in TEMP_FLAGS:
                    self.requires.append(FlagState("flag", visibility_flag, False))
                break
        # only "positive" requirements order steps: flag must be set, var ==/>/>= n or != its initial value
        # (plus the NPC's own visibility flag being clear, added above)
        for path_condition in path.conds:
            if path_condition.kind == "flag" and path_condition.flag in state_f and path_condition.value:
                self.requires.append(FlagState("flag", path_condition.flag, True))
            if path_condition.kind == "var" and path_condition.var in state_v and \
                    (path_condition.comparison in (CMP_EQ, CMP_GT, CMP_GE)
                     or (path_condition.comparison == CMP_NE and path_condition.value == VAR_INITIAL_VALUE)):
                self.requires.append(VarRequirement("var", path_condition.var, path_condition.comparison, path_condition.value))
            if path_condition.kind == "var" and path_condition.source and path_condition.source.kind == "has_item" and \
                    self.positive(path_condition): self.requires.append(ItemHeld("item", path_condition.source.item))

    @staticmethod
    def positive(path_condition):
        """Does the condition want a check (yes/no, has item, ...) to succeed?"""
        comparison_op, val = path_condition.comparison, path_condition.value
        return (comparison_op == CMP_EQ and val == TRUE) or (comparison_op == CMP_NE and val == FALSE) or \
               (comparison_op in (CMP_GT, CMP_GE) and val >= FALSE and COND_FN[comparison_op](TRUE, val))

    def has_substance(self):
        show = [effect for effect in self.path.effects if effect.kind not in ("say", "setvar", "addvar", "flag", "special")]
        return bool(show) or any(effect.kind == "say" for effect in self.path.effects)

    def story_pos(self):
        return self.analysis.story_pos(self.path)

    def var_rank(self):
        vals = [provided.value for provided in self.provides if provided.kind == "var"]
        return min(vals) if vals else 0

    # ---- rendering
    def trigger(self):
        game, analysis = self.analysis.game, self.analysis
        locs = analysis.where[self.script]
        kinds = Counter(location.kind for location in locs)
        kind = max(kinds, key=kinds.get)
        bymap = OrderedDict()
        for location in locs:
            if location.kind == kind: bymap.setdefault(location.map, []).append(location)
        first_map = next(iter(bymap))
        def place(map_info, locations):
            if kind == "mapscript": return game.mapname(map_info)
            return "%s %s" % (game.mapname(map_info), range_tiles([(location.x, location.y) for location in locations]))
        where = " / ".join(place(map_info, locations) for map_info, locations in list(bymap.items())[:MAX_LISTED_MAPS])
        if kind == "object":
            first_object = bymap[first_map][0]
            who = self.who(game.rom.u16(first_object.event_offset + OBJECT_EVENT_GRAPHICS_ID))
            if who in ("Poké Ball", "item ball", "fossil"):
                return "Pick up the %s at %s" % (who, where)
            return "Talk to %s at %s" % (who, where)
        if kind == "trigger": return "Walk onto %s" % where
        if kind == "sign": return "Check %s" % where
        return "Go to %s" % where

    def who_default(self):
        locs = self.analysis.where[self.script]
        for location in locs:
            if location.kind == "object":
                name = self.who(self.analysis.game.rom.u16(location.event_offset + OBJECT_EVENT_GRAPHICS_ID))
                return name[len("the "):] if name.startswith("the ") else name
        return "NPC" if not locs or locs[0].kind == "object" else "Text"

    def who(self, gfx):
        game = self.analysis.game
        speaker = next((effect.speaker for effect in self.path.effects if effect.kind == "say" and effect.speaker), None)
        if not speaker:
            speaker_counts = Counter(effect.speaker for path in self.analysis.paths[self.script] for effect in path.effects
                                     if effect.kind == "say" and effect.speaker and effect.speaker != "???")
            speaker = max(speaker_counts, key=speaker_counts.get) if speaker_counts else None
        if gfx & OBJ_EVENT_MON:
            return "the %s" % game.species(gfx & ~OBJ_EVENT_MON_FLAGS)
        name = EXPANSION_GFX_NAMES[gfx] if gfx < len(EXPANSION_GFX_NAMES) else None
        if name == "POKE_BALL": return "Poké Ball"
        if name == "ITEM_BALL": return "item ball"
        if name == "FOSSIL": return "fossil"
        if speaker: return speaker
        if name:
            base = re.sub(r"_(\d+|M|F)$", "", name)
            if base in GENERIC_SPRITES or name in GENERIC_SPRITES:
                nice = {"LINK_RECEPTIONIST": "receptionist", "MART_EMPLOYEE": "shop clerk",
                        "TUBER_M_SWIMMING": "swimming kid", "DEVON_EMPLOYEE": "employee",
                        "MOM": "woman", "QUINTY_PLUMP": "man"}.get(name, base.lower().replace("_", " "))
                return "the " + nice
        return "the NPC"

    def condition_texts(self):
        game, analysis, out = self.analysis.game, self.analysis, []
        path = self.path
        # time of day: combine all constraints on the time var
        for var_id, cons in path.cons.items():
            if path.src.get(var_id) == TIME_RESULT:
                matching_times = [time_index for time_index in range(len(TIMES))
                                  if all(COND_FN[comparison_op](time_index, val) for comparison_op, val in cons)]
                if 0 < len(matching_times) < len(TIMES):
                    out.append(" or ".join(TIMES[time_index] for time_index in matching_times))
        for path_condition in path.conds:
            if path_condition.kind == "var":
                var_id, comparison_op = path_condition.var, path_condition.comparison
                val, src = path_condition.value, path_condition.source
                if src is None:
                    if var_id == analysis.story_var:
                        story_sentence = self.story_text(comparison_op, val)
                        if story_sentence: out.append(story_sentence)
                    elif var_id not in self.state_v and var_id not in TEMP_VARS:
                        quest_id = analysis.var_from_quest.get((var_id, val)) if comparison_op == CMP_EQ else None
                        if quest_id is not None and quest_id != self.quest_id:
                            out.append("after finishing quest %d (%s)" % (quest_id + 1, game.qnames[quest_id]))
                    continue
                kind = src.kind
                pos = self.positive(path_condition)
                if kind == "yesno": out.append('answer "Yes"' if pos else 'answer "No"')
                elif kind == "has_item" and pos:
                    out.append("have %s%s" % ("%d× " % src.amount if src.amount > 1 else "", game.item(src.item)))
                elif kind == "species" and pos: out.append("have a %s in your party" % game.species(src.species))
                elif kind == "species": pass
                elif kind == "dex":
                    what = "caught" if src.caught else "seen"
                    out.append(("if you %s %s" if pos else "if you haven't %s %s") % (what, game.species(src.species)))
                elif kind == "menu" and comparison_op == CMP_EQ:
                    out.append('choose "%s"' % game.menu(src.menu, val))
                elif kind == "special" and pos: out.append("(game check: special %d passes)" % src.special)
                elif kind == "money" and pos: out.append("have at least ¥%d" % src.amount)
            elif path_condition.kind == "flag":
                flag_id, val = path_condition.flag, path_condition.value
                if isinstance(flag_id, TrainerFlag) or flag_id in self.state_f or flag_id in TEMP_FLAGS or not val: continue
                quest_id = analysis.flag_from_quest.get(flag_id)
                if quest_id is not None and quest_id != self.quest_id:
                    out.append("after finishing quest %d (%s)" % (quest_id + 1, game.qnames[quest_id]))
        return list(OrderedDict.fromkeys(out))

    def story_text(self, comparison_op, val):
        analysis = self.analysis
        need = val + 1 if comparison_op == CMP_GT else val if comparison_op in (CMP_EQ, CMP_GE) else None
        if need is None or need <= 0: return None
        for script, path in analysis.pick_story(need)[:1]:   # the main story path only
            first_location = analysis.where[script][0]
            return "after the story event in %s (story step %d)" % (analysis.game.mapname(first_location.map), need)
        return "after story step %d" % need

    def action_texts(self):
        game, analysis, out = self.analysis.game, self.analysis, []
        says = [i for i, effect in enumerate(self.path.effects)
                if effect.kind == "say" and len(clean_text(effect.text)) > MIN_QUOTE_LENGTH
                and not (RECEIPT_RE.match(clean_text(effect.text)) and "?" not in effect.text)]
        quote_at = set(says[:1] + says[-1:])           # the first and the last quotable line
        lines_skipped = len(says) > len(quote_at)      # there are quotable lines in between
        default_who = self.who_default()
        for i, effect in enumerate(self.path.effects):
            effect_kind = effect.kind
            if effect_kind == "say":
                text = clean_text(effect.text)
                match = RECEIPT_RE.match(text) if "?" not in text else None
                if match and len(text) < MAX_RECEIPT_LENGTH:
                    what = match.group("what").rstrip("!.")
                    if text.startswith("You registered"):
                        out.append("New phone contact: %s" % what); continue
                    if not any(earlier_line.startswith(RECEIVE_PREFIX)
                               and (received_name(earlier_line) in what or what in earlier_line) for earlier_line in out):
                        out.append(RECEIVE_PREFIX + what)
                elif i in quote_at:
                    if lines_skipped and i == says[-1]: out.append("…")
                    out.append('%s: "%s"' % (effect.speaker or default_who, shorten(text)))
            elif effect_kind == "phone":
                phone_text = clean_text(effect.text)
                phone_text = re.sub(r"^.*?Beep!\s*", "", phone_text); phone_text = re.sub(r"\s*Click!.*$", "", phone_text)
                out.append('Phone call: "%s"' % shorten(phone_text))
            elif effect_kind == "trainer":
                name = (analysis.trainer_name(effect.trainer) if analysis.trainer_name else "") or effect.speaker
                out.append("Battle %s (trainer #%d)" % (name, effect.trainer) if name else "Battle trainer #%d" % effect.trainer)
            elif effect_kind == "wild": out.append("Battle a wild %s (Lv%d)" % (game.species(effect.species), effect.level))
            elif effect_kind in ("give_item", "find_item"):
                out.append("Receive %s%s" % (game.item(effect.item), " ×%d" % effect.amount if effect.amount > 1 else ""))
            elif effect_kind == "take_item":
                out.append("Hand over %s%s" % (game.item(effect.item), " ×%d" % effect.amount if effect.amount > 1 else ""))
            elif effect_kind == "give_mon": out.append("Receive %s (Lv%d)" % (game.species(effect.species), effect.level))
            elif effect_kind == "give_egg": out.append("Receive a %s Egg" % game.species(effect.species))
            elif effect_kind == "money": out.append("Receive ¥%d" % effect.amount if effect.amount > 0 else "Pay ¥%d" % -effect.amount)
            elif effect_kind == "warp": out.append("You're taken to %s" % game.mapname(effect.map))
            elif effect_kind == "quest" and effect.quest != self.quest_id:
                out.append("%s quest %d (%s)" % (QUEST_CASE_VERBS[effect.case], effect.quest + 1, game.qnames[effect.quest]))
        return list(OrderedDict.fromkeys(out))

    def needed_items(self):
        out = []
        for path_condition in self.path.conds:
            if checks_result(path_condition, "has_item") and self.positive(path_condition):
                out.append(path_condition.source.item)
        return list(OrderedDict.fromkeys(out))

    def needed_species(self):
        return list(OrderedDict.fromkeys(path_condition.source.species for path_condition in self.path.conds
                                         if checks_result(path_condition, "species") and self.positive(path_condition)))

    def key(self):
        return (self.role, self.trigger(), tuple(self.condition_texts()), tuple(self.action_texts()))


def received_name(line):
    """'Receive Old Rod (x2)' -> 'Old Rod'"""
    name, _, _ = line[len(RECEIVE_PREFIX):].partition(" (")
    return name


def checks_result(path_condition, kind):
    """Is this a condition on a result var of the given kind (has_item, species, ...)?"""
    return path_condition.kind == "var" and bool(path_condition.source) and path_condition.source.kind == kind


def satisfies(provided, requirement):
    """Does a step that provides `provided` make `requirement` true?"""
    if requirement.kind == "flag":
        return provided.kind == "flag" and provided.flag == requirement.flag and provided.value == requirement.value
    if requirement.kind == "item": return provided.kind == "item" and provided.item == requirement.item
    if requirement.kind == "var":
        if provided.kind != "var" or provided.var != requirement.var \
                or not COND_FN[requirement.comparison](provided.value, requirement.value): return False
        return provided.value != VAR_INITIAL_VALUE   # setting a var back to its initial value never moves a quest on
    return False


IMPORTANT = ("trainer", "wild", "give_item", "find_item", "take_item", "give_mon", "give_egg", "money",
             "warp", "quest", "setvar", "addvar", "flag")


def order_steps(analysis, steps, state_v):
    # 1. merge paths of the same script that do the same things (e.g. "nickname it? yes/no")
    groups = OrderedDict()
    for step in steps:
        step_key = (step.role, step.script, tuple(effect for effect in step.path.effects if effect.kind in IMPORTANT))
        groups.setdefault(step_key, []).append(step)
    merged = []
    for members in groups.values():
        step = members[0]
        conds = [condition for condition in step.condition_texts() if all(condition in member.condition_texts() for member in members[1:])]
        step.merged_conds = conds
        for member in members[1:]:
            step.provides |= member.provides
        merged.append(step)
    steps, step_count = merged, len(merged)
    # 2. dependency edges and levels
    succ = defaultdict(set)
    for i in range(step_count):
        for j in range(step_count):
            if i != j and any(satisfies(provided, requirement) for provided in steps[i].provides for requirement in steps[j].requires):
                succ[i].add(j)
    level = [0] * step_count
    for _ in range(step_count):
        changed = False
        for i in range(step_count):
            for j in succ[i]:
                if level[j] < level[i] + 1 <= step_count:
                    level[j] = level[i] + 1; changed = True
        if not changed: break
    def reach(src):
        seen, todo = set(), list(src)
        while todo:
            i = todo.pop()
            for j in succ[i]:
                if j not in seen: seen.add(j); todo.append(j)
        return seen
    starts = [i for i in range(step_count) if steps[i].role == "start"]
    dones = [i for i in range(step_count) if steps[i].role in ("done", "final")]
    after = reach(dones) - set(dones) - set(starts)
    # steps that lead to a start are prerequisites
    pred = defaultdict(set)
    for i in range(step_count):
        for j in succ[i]: pred[j].add(i)
    pre, todo = set(), list(starts)
    while todo:
        j = todo.pop()
        for i in pred[j]:
            if i not in pre and steps[i].role not in ("start", "done", "final"): pre.add(i); todo.append(i)
    pre -= after
    pre -= reach(starts)          # repeatable events (re-racing etc.) aren't prerequisites
    # several ways to start from the same NPC: keep the one the rest of the quest builds on
    drop = set()
    by_script = defaultdict(list)
    for i in starts: by_script[steps[i].script].append(i)
    for script, idx in by_script.items():
        if len(idx) == 1: continue
        useful = [i for i in idx if succ[i] - set(idx)] or idx
        best = min(useful, key=lambda i: (len(steps[i].merged_conds), -len(succ[i])))
        drop |= set(idx) - {best}
    def group(i):
        step = steps[i]
        if step.role == "unlock" or i in pre: return GROUP_BEFORE_START
        if step.role == "start": return GROUP_START
        if i in after: return GROUP_AFTERWARDS
        if step.role in ("done", "final"): return GROUP_COMPLETE
        return GROUP_MIDDLE
    def key(i):
        step = steps[i]
        story_position = step.story_pos()
        return (group(i), story_position if story_position is not None else 0, level[i], step.var_rank(), step.script)
    out, seen = [], set()
    for i in sorted(range(step_count), key=key):
        if i in drop: continue
        step = steps[i]
        step.after_done = group(i) == GROUP_AFTERWARDS
        if group(i) == GROUP_BEFORE_START and step.role == "step": step.role = "unlock"
        step_key = (step.role, step.trigger(), tuple(step.merged_conds), tuple(step.action_texts()))
        if step_key in seen: continue
        seen.add(step_key); out.append(step)
    return out


# --------------------------------------------------------------- output --
def where_to_find(game, item_id, limit=MAX_ITEM_LOCATIONS):
    name = game.item(item_id)
    rows = [row for row in game.items_csv if row["itemName"] == name]
    good = [row for row in rows if not row["source"].endswith("?")]
    rows = good or rows
    out = []
    for row in rows[:limit]:
        src = {"itemBall": "item ball", "hidden": "hidden item", "gift": "given by an NPC",
               "found": "found", "gift?": "given (unconfirmed)", "found?": "found (unconfirmed)"}.get(row["source"], row["source"])
        location = "%s (%s)%s" % (row["route"], row["mapId"], " %s,%s" % (row["x"], row["y"]) if row["x"] else "")
        out.append("%s: %s" % (src, location))
    if len(rows) > limit: out.append("+%d more" % (len(rows) - limit))
    return out


def where_to_catch(game, species_id, limit=MAX_CATCH_LOCATIONS):
    name = game.species(species_id)
    rows = [row for row in game.enc_csv if row["pokemonName"] == name]
    rows.sort(key=lambda row: -float(row["encounterRate"] or 0))
    return ["%s, %s %s%%" % (row["route"], row["encounterType"], row["encounterRate"]) for row in rows[:limit]]


def render(analysis, quest_id, steps, markdown_lines, rows):
    game = analysis.game
    quest_offset = game.quest_table + SIDE_QUEST_SIZE * quest_id
    desc = decode(game.rom, game.rom.off(game.rom.u32(quest_offset + SIDE_QUEST_DESCRIPTION)))
    done = decode(game.rom, game.rom.off(game.rom.u32(quest_offset + SIDE_QUEST_DONE_DESCRIPTION)))
    loc = decode(game.rom, game.rom.off(game.rom.u32(quest_offset + SIDE_QUEST_MAP)))
    markdown_lines.append('## %d. "%s"\n' % (quest_id + 1, game.qnames[quest_id]))
    markdown_lines.append("_%s_ — quest menu location: %s\n" % (desc, loc))
    if not steps:
        markdown_lines.append("_No script starts or completes this quest._\n")
    has_done = any(any_step.role == "done" for any_step in steps)
    step_number, after_hdr = 0, False
    for step in steps:
        if step.after_done and not after_hdr:
            markdown_lines.append("\n**Afterwards:**\n"); after_hdr = True
        step_number += 1
        label = {"unlock": "Before starting", "start": "Start", "done": "Complete", "story": "Story", "step": "",
                 "final": "Finish"}[step.role]
        conds = getattr(step, "merged_conds", None)
        if conds is None: conds = step.condition_texts()
        fin = [condition for condition in conds if condition.startswith("after finishing quest ")]
        if len(fin) > MAX_SEPARATE_QUEST_PREREQUISITES:
            nums = sorted(int(FINISHED_QUEST_RE.match(condition).group("number")) for condition in fin)
            conds = [condition for condition in conds if condition not in fin]
            conds.insert(0, "after finishing quests %s (%d quests)" % (", ".join(map(str, nums)), len(nums)))
        head = step.trigger()
        if conds: head += " — " + ", ".join(conds)
        markdown_lines.append("%d. %s%s" % (step_number, "**%s:** " % label if label else "", head))
        sub = " " * len("%d. " % step_number)      # nested bullets must line up with the item text (10. needs 4 spaces)
        acts = step.action_texts()
        for action in acts: markdown_lines.append(sub + "- " + action)
        for item_id in step.needed_items():
            locations = where_to_find(game, item_id)
            markdown_lines.append(sub + "- Where to find %s: %s" % (
                game.item(item_id), "; ".join(locations) if locations else "not in items.csv (shop, berry tree or native code?)"))
        for species_id in step.needed_species():
            locations = where_to_catch(game, species_id)
            markdown_lines.append(sub + "- Where to catch %s: %s" % (
                game.species(species_id), "; ".join(locations) if locations else "no wild encounter found"))
        first_location = analysis.where[step.script][0]
        map_info = first_location.map
        rows.append([quest_id + 1, game.qnames[quest_id], step_number, step.role + ("/after" if step.after_done else ""),
                     game.mapname(map_info), "%d.%d" % (map_info.group, map_info.num), first_location.x, first_location.y,
                     head, " | ".join(acts), "0x%X" % (step.script + ROM_BASE)])
    if not has_done and steps:
        markdown_lines.append("\n_No script marks this quest as completed in the quest menu._")
    # items the quest scripts check for that no step above explains
    shown = {item_id for step in steps for item_id in step.needed_items()}
    extra = []
    for path in analysis.quest_paths_all(quest_id):
        for path_condition in path.conds:
            if checks_result(path_condition, "has_item") and Step.positive(path_condition) \
                    and path_condition.source.item not in shown:
                shown.add(path_condition.source.item); extra.append(path_condition.source.item)
    for item_id in extra:
        locations = where_to_find(game, item_id)
        markdown_lines.append("\n- Also needed: **%s** — %s" % (game.item(item_id), "; ".join(locations) if locations else "not in items.csv"))
    markdown_lines.append("")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    here = os.path.dirname(os.path.abspath(__file__))
    parser.add_argument("rom", nargs="?", default=os.path.join(here, "input", "game.gba"))
    parser.add_argument("-o", "--output", default=os.path.join(here, "output", "quest_steps.md"),
                    help="markdown file; a .csv with the same name is written next to it")
    parser.add_argument("--quest", type=int, action="append", help="only this quest (1-based); repeatable")
    parser.add_argument("--bulk", type=int, default=DEFAULT_BULK, help="ignore paths that change more flags/vars than this")
    args = parser.parse_args()
    log = lambda *parts: print(*parts, file=sys.stderr)
    rom = Rom(args.rom)
    game = Game(rom, here)
    log("quests            : %d" % game.quest_count)
    log("natives recognised: %s" % {hex(native_pointer): kind for native_pointer, kind in game.native_kind.items()})
    analysis = Analysis(game, bulk=args.bulk)
    log("scripts / paths   : %d / %d" % (len(analysis.paths), sum(len(script_paths) for script_paths in analysis.paths.values())))
    log("story variable    : %s" % ("VAR_%04X" % analysis.story_var if analysis.story_var is not None else "-"))
    log("trainer names     : %s" % ("found" if analysis.trainer_name else "not found"))
    markdown_lines = ["# Quest walkthrough", "",
          "Generated by `extract_quest_steps.py` from the ROM's event scripts. Locations are "
          "`Map name (group.num) x,y`, the tile coordinates Porymap shows. "
          "Quotes are the first and last line of dialogue of that step.", ""]
    rows = []
    wanted = [quest_number - 1 for quest_number in args.quest] if args.quest else range(game.quest_count)
    for quest_id in wanted:
        steps = analysis.quest_steps(quest_id)
        render(analysis, quest_id, steps, markdown_lines, rows)
        log("quest %2d: %2d steps  %s" % (quest_id + 1, len(steps), game.qnames[quest_id]))
    os.makedirs(os.path.dirname(os.path.abspath(args.output)), exist_ok=True)
    text = re.sub(r"\n{3,}", "\n\n", "\n".join(markdown_lines)).rstrip("\n") + "\n"
    with open(args.output, "w", encoding="utf-8") as output_file: output_file.write(text)
    output_base, _ = os.path.splitext(args.output)
    csv_path = output_base + ".csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as output_file:
        writer = csv.writer(output_file)
        writer.writerow(["questNumber", "questName", "step", "role", "location", "mapId", "x", "y", "what", "details", "script"])
        writer.writerows(rows)
    log("wrote %s and %s" % (args.output, csv_path))


if __name__ == "__main__":
    main()
