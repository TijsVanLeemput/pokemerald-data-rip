#!/usr/bin/env python3
"""
Quest extractor for pokeemerald(-expansion) ROM hacks that use the
PokemonSanFran "Unbound Quest Menu" (sSideQuests / struct SideQuest).

Usage:
    python3 extract_quests.py [input/game.gba] [-o output/quests.csv]

Writes
    output/quests.csv        one row per quest (name, descriptions, location, sprite,
                             and where the quest is started / completed)
    output/quest_events.csv  one row per `questmenu` script command found in the
                             map scripts (unlock, start, reward, complete, checks)
    output/subquests.csv     only when the hack defines subquests

The quest table is found by scanning the ROM for an array of
    struct SideQuest { const u8 *name, *desc, *donedesc, *map; u16 sprite;
                       u8 spritetype; const struct SubQuest *subquests; u8 numSubquests; }
(28 bytes per entry on the GBA). Use --quest-table to force the address.

Needs extract_encounters.py and extract_items.py in the same folder.
"""
import argparse, csv, os, re, struct, sys, bisect
from collections import Counter, OrderedDict, defaultdict, namedtuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from extract_encounters import (Rom, ROM_BASE, CHARMAP, TEXT_END, CHAR_NEWLINE, CHAR_PROMPT_SCROLL, CHAR_PROMPT_CLEAR,
                                EXT_CTRL_CODE_BEGIN, PLACEHOLDER_BEGIN, CONTROL_SEQUENCE_LENGTH,
                                MAP_HEADER_REGION_MAP_SECTION, POINTER_SIZE, POKEMON_NAME_LENGTH,
                                find_species, find_map_groups, find_region_map_entries, mapsec_names)
from extract_items import (ScriptCmd, CMD_LEN, MAX_SCRIPT_DISTANCE, command_args, find_items, iter_maps,
                           collect_entries, Walker, learn_native_args)

# struct SideQuest { const u8 *name, *desc, *donedesc, *map; u16 sprite; u8 spritetype;
#                    const struct SubQuest *subquests; u8 numSubquests; }
SIDE_QUEST_SIZE = 28
SIDE_QUEST_NAME, SIDE_QUEST_DESCRIPTION, SIDE_QUEST_DONE_DESCRIPTION, SIDE_QUEST_MAP = 0, 4, 8, 12
SIDE_QUEST_SPRITE, SIDE_QUEST_SPRITE_TYPE = 16, 18
SIDE_QUEST_SUBQUESTS, SIDE_QUEST_SUBQUEST_COUNT = 20, 24
SIDE_QUEST_TEXT_FIELDS = (SIDE_QUEST_NAME, SIDE_QUEST_DESCRIPTION, SIDE_QUEST_DONE_DESCRIPTION, SIDE_QUEST_MAP)
# struct SubQuest { u8 id; const u8 *name, *desc, *map; u16 sprite; u8 spritetype; const u8 *type; }
SUB_QUEST_SIZE = 24
SUB_QUEST_ID, SUB_QUEST_NAME, SUB_QUEST_DESCRIPTION, SUB_QUEST_MAP = 0, 4, 8, 12
SUB_QUEST_SPRITE, SUB_QUEST_SPRITE_TYPE, SUB_QUEST_LABEL = 16, 18, 20
MAX_SUBQUESTS = 100                       # sanity bound while scanning for the quest table
QUEST_MAP_NAME_MIN_LENGTH, QUEST_MAP_NAME_MAX_LENGTH = 2, 30
MAX_QUEST_TEXT_LENGTH = 400               # quest texts must end within this many bytes
MAX_TEXT_LENGTH = 600                     # default read limit for decode()

SPRITE_TYPE_OBJECT, SPRITE_TYPE_ITEM, SPRITE_TYPE_POKEMON = 1, 2, 3
SPRITE_TYPES = {SPRITE_TYPE_OBJECT: "object", SPRITE_TYPE_ITEM: "item", SPRITE_TYPE_POKEMON: "pokemon"}

# questmenu <case>, <questId>  (include/constants/quests.h)
(QUEST_CASE_OPEN_MENU, QUEST_CASE_UNLOCK, QUEST_CASE_START, QUEST_CASE_REWARD, QUEST_CASE_COMPLETE,
 QUEST_CASE_CHECK_UNLOCKED, QUEST_CASE_CHECK_INACTIVE, QUEST_CASE_CHECK_ACTIVE, QUEST_CASE_CHECK_REWARD,
 QUEST_CASE_CHECK_COMPLETE, QUEST_CASE_BUFFER_NAME) = range(11)
QUEST_CASES = {
    QUEST_CASE_OPEN_MENU: "openMenu", QUEST_CASE_UNLOCK: "unlock", QUEST_CASE_START: "start",
    QUEST_CASE_REWARD: "reward", QUEST_CASE_COMPLETE: "complete",
    QUEST_CASE_CHECK_UNLOCKED: "checkUnlocked", QUEST_CASE_CHECK_INACTIVE: "checkInactive",
    QUEST_CASE_CHECK_ACTIVE: "checkActive", QUEST_CASE_CHECK_REWARD: "checkReward",
    QUEST_CASE_CHECK_COMPLETE: "checkComplete", QUEST_CASE_BUFFER_NAME: "bufferName",
}
ACTION_ORDER = {action: rank for rank, action in enumerate(QUEST_CASES.values())}
QUESTMENU_OPCODE_DEFAULT = ScriptCmd.QUESTMENU
# startquest / completequest macro: closemessage; delay 30; questmenu START or COMPLETE, q; questmenu BUFFER_NAME, q
MACRO_DELAY_FRAMES = 30
MACRO_RE = re.compile(
    re.escape(struct.pack("<BBH", ScriptCmd.CLOSEMESSAGE, ScriptCmd.DELAY, MACRO_DELAY_FRAMES))
    + b"(?P<opcode>.)(?P<case>[" + re.escape(bytes([QUEST_CASE_START, QUEST_CASE_COMPLETE])) + b"])(?P<quest>.)"
    + b"(?P=opcode)" + re.escape(bytes([QUEST_CASE_BUFFER_NAME])) + b"(?P=quest)", re.S)
MACRO_QUESTMENU_AT = CMD_LEN[ScriptCmd.CLOSEMESSAGE] + CMD_LEN[ScriptCmd.DELAY]   # the first questmenu in the macro

QuestEvent = namedtuple("QuestEvent", "quest_number quest_name action route map_id x y event_kind script_address")
QUEST_EVENT_COLUMNS = ["questNumber", "questName", "action", "route", "mapId", "x", "y", "eventKind", "scriptAddress"]

# expansion object-event pokemon sprites: OBJ_EVENT_MON | species (+ shiny/female bits)
OBJ_EVENT_MON, OBJ_EVENT_MON_SHINY, OBJ_EVENT_MON_FEMALE = 1 << 14, 1 << 13, 1 << 12
OBJ_EVENT_MON_FLAGS = OBJ_EVENT_MON | OBJ_EVENT_MON_SHINY | OBJ_EVENT_MON_FEMALE

# OBJ_EVENT_GFX_* names from pokeemerald-expansion 1.13.2 (ids 0-241). A hack can
# redraw these or add its own ids above 241, so treat the name as a hint only.
EXPANSION_GFX_NAMES = (
    "BRENDAN_NORMAL BRENDAN_MACH_BIKE BRENDAN_SURFING BRENDAN_FIELD_MOVE QUINTY_PLUMP NINJA_BOY "
    "TWIN BOY_1 GIRL_1 BOY_2 GIRL_2 LITTLE_BOY LITTLE_GIRL BOY_3 GIRL_3 RICH_BOY WOMAN_1 FAT_MAN "
    "POKEFAN_F MAN_1 WOMAN_2 EXPERT_M EXPERT_F MAN_2 WOMAN_3 POKEFAN_M WOMAN_4 COOK "
    "LINK_RECEPTIONIST OLD_MAN OLD_WOMAN CAMPER PICNICKER MAN_3 WOMAN_5 YOUNGSTER BUG_CATCHER "
    "PSYCHIC_M SCHOOL_KID_M MANIAC HEX_MANIAC RAYQUAZA_STILL SWIMMER_M SWIMMER_F BLACK_BELT "
    "BEAUTY SCIENTIST_1 LASS GENTLEMAN SAILOR FISHERMAN RUNNING_TRIATHLETE_M "
    "RUNNING_TRIATHLETE_F TUBER_F TUBER_M HIKER CYCLING_TRIATHLETE_M CYCLING_TRIATHLETE_F NURSE "
    "ITEM_BALL BERRY_TREE BERRY_TREE_EARLY_STAGES BERRY_TREE_LATE_STAGES BRENDAN_ACRO_BIKE "
    "PROF_BIRCH MAN_4 MAN_5 REPORTER_M REPORTER_F BARD ANABEL TUCKER GRETA SPENSER NOLAND LUCY "
    "UNUSED_NATU_DOLL UNUSED_MAGNEMITE_DOLL UNUSED_SQUIRTLE_DOLL UNUSED_WOOPER_DOLL "
    "UNUSED_PIKACHU_DOLL UNUSED_PORYGON2_DOLL CUTTABLE_TREE MART_EMPLOYEE ROOFTOP_SALE_WOMAN "
    "TEALA BREAKABLE_ROCK PUSHABLE_BOULDER MR_BRINEYS_BOAT MAY_NORMAL MAY_MACH_BIKE "
    "MAY_ACRO_BIKE MAY_SURFING MAY_FIELD_MOVE TRUCK VIGOROTH_CARRYING_BOX VIGOROTH_FACING_AWAY "
    "BIRCHS_BAG ZIGZAGOON_1 ARTIST RIVAL_BRENDAN_NORMAL RIVAL_BRENDAN_MACH_BIKE "
    "RIVAL_BRENDAN_ACRO_BIKE RIVAL_BRENDAN_SURFING RIVAL_BRENDAN_FIELD_MOVE RIVAL_MAY_NORMAL "
    "RIVAL_MAY_MACH_BIKE RIVAL_MAY_ACRO_BIKE RIVAL_MAY_SURFING RIVAL_MAY_FIELD_MOVE CAMERAMAN "
    "BRENDAN_UNDERWATER MAY_UNDERWATER MOVING_BOX CABLE_CAR SCIENTIST_2 DEVON_EMPLOYEE "
    "AQUA_MEMBER_M AQUA_MEMBER_F MAGMA_MEMBER_M MAGMA_MEMBER_F SIDNEY PHOEBE GLACIA DRAKE "
    "ROXANNE BRAWLY WATTSON FLANNERY NORMAN WINONA LIZA TATE WALLACE STEVEN WALLY LITTLE_BOY_3 "
    "BRENDAN_FISHING MAY_FISHING HOT_SPRINGS_OLD_WOMAN SS_TIDAL SUBMARINE_SHADOW PICHU_DOLL "
    "PIKACHU_DOLL MARILL_DOLL TOGEPI_DOLL CYNDAQUIL_DOLL CHIKORITA_DOLL TOTODILE_DOLL "
    "JIGGLYPUFF_DOLL MEOWTH_DOLL CLEFAIRY_DOLL DITTO_DOLL SMOOCHUM_DOLL TREECKO_DOLL "
    "TORCHIC_DOLL MUDKIP_DOLL DUSKULL_DOLL WYNAUT_DOLL BALTOY_DOLL KECLEON_DOLL AZURILL_DOLL "
    "SKITTY_DOLL SWABLU_DOLL GULPIN_DOLL LOTAD_DOLL SEEDOT_DOLL PIKA_CUSHION ROUND_CUSHION "
    "KISS_CUSHION ZIGZAG_CUSHION SPIN_CUSHION DIAMOND_CUSHION BALL_CUSHION GRASS_CUSHION "
    "FIRE_CUSHION WATER_CUSHION BIG_SNORLAX_DOLL BIG_RHYDON_DOLL BIG_LAPRAS_DOLL "
    "BIG_VENUSAUR_DOLL BIG_CHARIZARD_DOLL BIG_BLASTOISE_DOLL BIG_WAILMER_DOLL BIG_REGIROCK_DOLL "
    "BIG_REGICE_DOLL BIG_REGISTEEL_DOLL LATIAS LATIOS GAMEBOY_KID CONTEST_JUDGE BRENDAN_WATERING "
    "MAY_WATERING BRENDAN_DECORATING MAY_DECORATING ARCHIE MAXIE KYOGRE_FRONT GROUDON_FRONT "
    "FOSSIL REGIROCK REGICE REGISTEEL SKITTY KECLEON KYOGRE_ASLEEP GROUDON_ASLEEP RAYQUAZA "
    "ZIGZAGOON_2 PIKACHU AZUMARILL WINGULL KECLEON_BRIDGE_SHADOW TUBER_M_SWIMMING AZURILL MOM "
    "LINK_BRENDAN LINK_MAY JUAN SCOTT POOCHYENA KYOGRE_SIDE GROUDON_SIDE MYSTERY_GIFT_MAN "
    "TRICK_HOUSE_STATUE KIRLIA DUSCLOPS UNION_ROOM_NURSE SUDOWOODO MEW RED LEAF DEOXYS "
    "DEOXYS_TRIANGLE BRANDON LINK_RS_BRENDAN LINK_RS_MAY LUGIA HOOH POKE_BALL OW_MON "
    "LIGHT_SPRITE"
).split()

# extra characters that show up in longer texts
TEXT_EXTRA = {0x01: "À", 0x02: "Á", 0x03: "Â", 0x04: "Ç", 0x05: "È", 0x06: "É", 0x07: "Ê", 0x08: "Ë",
              0x09: "Ì", 0x0B: "Î", 0x0C: "Ï", 0x0D: "Ò", 0x0E: "Ó", 0x0F: "Ô", 0x10: "Œ", 0x11: "Ù",
              0x12: "Ú", 0x13: "Û", 0x14: "Ñ", 0x15: "ß", 0x16: "à", 0x17: "á", 0x19: "ç", 0x1A: "è",
              0x1C: "ê", 0x1D: "ë", 0x1E: "ì", 0x20: "î", 0x21: "ï", 0x22: "ò", 0x23: "ó", 0x24: "ô",
              0x25: "œ", 0x26: "ù", 0x27: "ú", 0x28: "û", 0x29: "ñ", 0x2A: "º", 0x2B: "ª", 0x2E: "+",
              0x5B: "%", 0x5C: "(", 0x5D: ")", 0x34: "Lv", 0x35: "=", 0x36: ";",
              0x51: "¿", 0x52: "¡", 0xB7: "¥", 0xB9: "×", 0xF1: "Ä", 0xF2: "Ö",
              0xF3: "Ü", 0xF4: "ä", 0xF5: "ö", 0xF6: "ü"}
PLACEHOLDERS = {0x01: "{PLAYER}", 0x02: "{STR_VAR_1}", 0x03: "{STR_VAR_2}",
                0x04: "{STR_VAR_3}", 0x06: "{RIVAL}"}
# argument bytes of the EXT_CTRL_CODE_BEGIN control codes (by code id)
FC_ARGS = {0x04: 3, 0x0B: 2, 0x10: 2, 0x07: 0, 0x09: 0, 0x0A: 0, 0x0F: 0, 0x15: 0,
           0x16: 0, 0x17: 0, 0x18: 0}
DEFAULT_FC_ARGS = 1


def decode(rom, offset, maxlen=MAX_TEXT_LENGTH, newline=" "):
    """Full-length game text -> str. Line breaks become `newline`; unknown bytes
    are kept as [XX] so nothing disappears silently."""
    data, out, i = rom.data, [], offset
    while i < min(offset + maxlen, rom.size):
        char_code = data[i]
        if char_code == TEXT_END: break
        if char_code in (CHAR_NEWLINE, CHAR_PROMPT_SCROLL, CHAR_PROMPT_CLEAR): out.append(newline); i += 1; continue
        if char_code == EXT_CTRL_CODE_BEGIN:
            code_id = data[i + 1]
            i += CONTROL_SEQUENCE_LENGTH + FC_ARGS.get(code_id, DEFAULT_FC_ARGS); continue
        if char_code == PLACEHOLDER_BEGIN:
            placeholder_id = data[i + 1]
            out.append(PLACEHOLDERS.get(placeholder_id, "{VAR_%02X}" % placeholder_id)); i += CONTROL_SEQUENCE_LENGTH; continue
        character = CHARMAP.get(char_code, TEXT_EXTRA.get(char_code))
        out.append(character if character is not None else "[%02X]" % char_code)
        i += 1
    text = "".join(out)
    return re.sub(r"[ ]{2,}", " ", text).strip() if newline == " " else text.strip()


# ------------------------------------------------------------- quest table --
def text_ptr_ok(rom, pointer, maxlen=MAX_QUEST_TEXT_LENGTH):
    """A pointer to a non-empty string that ends within maxlen bytes."""
    if not rom.isptr(pointer): return False
    offset = rom.off(pointer)
    seg = rom.data[offset:offset + maxlen]
    return TEXT_END in seg and seg.index(TEXT_END) > 0


def side_quest_ok(rom, offset):
    if offset + SIDE_QUEST_SIZE > rom.size: return False
    if not all(text_ptr_ok(rom, rom.u32(offset + field)) for field in SIDE_QUEST_TEXT_FIELDS): return False
    if rom.data[offset + SIDE_QUEST_SPRITE_TYPE] not in SPRITE_TYPES: return False
    if not rom.is_clean_text(rom.off(rom.u32(offset + SIDE_QUEST_MAP)), QUEST_MAP_NAME_MIN_LENGTH, QUEST_MAP_NAME_MAX_LENGTH):
        return False
    subquests_pointer = rom.u32(offset + SIDE_QUEST_SUBQUESTS)
    subquest_count = rom.data[offset + SIDE_QUEST_SUBQUEST_COUNT]
    if subquests_pointer == 0: return subquest_count == 0
    return rom.isptr(subquests_pointer) and 0 < subquest_count < MAX_SUBQUESTS


def find_quest_table(rom):
    """Longest run of SideQuest-shaped entries. Returns (offset, count)."""
    best_offset, best_count, offset = None, 0, 0
    while offset < rom.size - SIDE_QUEST_SIZE:
        if side_quest_ok(rom, offset):
            run_length, probe_offset = 0, offset
            while side_quest_ok(rom, probe_offset): run_length += 1; probe_offset += SIDE_QUEST_SIZE
            if run_length > best_count: best_offset, best_count = offset, run_length
            offset = probe_offset
        else:
            offset += POINTER_SIZE
    return best_offset, best_count


# ---------------------------------------------------------------- sprites --
def sprite_label(sprite, stype, species_name, item_name):
    if stype == SPRITE_TYPE_ITEM:
        return "item", item_name(sprite)
    if stype == SPRITE_TYPE_POKEMON:
        return "pokemon", species_name(sprite)
    if sprite & OBJ_EVENT_MON:
        species_id = sprite & ~OBJ_EVENT_MON_FLAGS
        tags = [tag for flag_bit, tag in ((OBJ_EVENT_MON_SHINY, "shiny"), (OBJ_EVENT_MON_FEMALE, "female"))
                if sprite & flag_bit]
        return "object (pokemon)", species_name(species_id) + (" (%s)" % ", ".join(tags) if tags else "")
    if sprite < len(EXPANSION_GFX_NAMES):
        return "object", EXPANSION_GFX_NAMES[sprite]
    return "object", "hack gfx #%d" % sprite


# ------------------------------------------------------------------- main --
def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    here = os.path.dirname(os.path.abspath(__file__))
    parser.add_argument("rom", nargs="?", default=os.path.join(here, "input", "game.gba"))
    parser.add_argument("-o", "--output", default=os.path.join(here, "output", "quests.csv"),
                    help="quests CSV; quest_events.csv / subquests.csv go next to it")
    parser.add_argument("--quest-table", type=lambda text: int(text, 0), help="force sSideQuests offset")
    parser.add_argument("--quest-count", type=int, help="force the number of quests")
    parser.add_argument("--questmenu-opcode", type=lambda text: int(text, 0),
                    help="script opcode of `questmenu` (auto-detected, 0x%X here)" % QUESTMENU_OPCODE_DEFAULT)
    parser.add_argument("--map-groups", type=lambda text: int(text, 0))
    parser.add_argument("--region-map-entries", type=lambda text: int(text, 0))
    parser.add_argument("--keep-newlines", action="store_true",
                    help="keep the in-game line breaks in descriptions (as \\n)")
    args = parser.parse_args()
    log = lambda *parts: print(*parts, file=sys.stderr)
    rom = Rom(args.rom)
    newline = "\n" if args.keep_newlines else " "

    # --- lookups
    species_base, sstride, snoff, _, scount = find_species(rom)
    species_name = lambda species_id: (rom.text(species_base + sstride * species_id + snoff, POKEMON_NAME_LENGTH + 1)
                                       if 0 < species_id < scount else "SPECIES_%d" % species_id)
    _, _, _, item_name = find_items(rom)

    # --- quest table
    if args.quest_table is not None:
        quest_table = args.quest_table
        quest_count = args.quest_count or 0
        if not quest_count:
            while side_quest_ok(rom, quest_table + SIDE_QUEST_SIZE * quest_count): quest_count += 1
    else:
        quest_table, quest_count = find_quest_table(rom)
        if quest_table is None: raise SystemExit("No Unbound-style quest table (struct SideQuest) found")
        if args.quest_count: quest_count = args.quest_count
    log("sSideQuests       @ 0x%X  (%d quests, %d bytes each)" % (quest_table, quest_count, SIDE_QUEST_SIZE))

    quests, subrows = [], []
    for i in range(quest_count):
        quest_offset = quest_table + SIDE_QUEST_SIZE * i
        name, desc, done, location_offset = (rom.off(rom.u32(quest_offset + field)) for field in SIDE_QUEST_TEXT_FIELDS)
        sprite, stype = rom.u16(quest_offset + SIDE_QUEST_SPRITE), rom.data[quest_offset + SIDE_QUEST_SPRITE_TYPE]
        subquests_pointer = rom.u32(quest_offset + SIDE_QUEST_SUBQUESTS)
        nsub = rom.data[quest_offset + SIDE_QUEST_SUBQUEST_COUNT]
        kind, label = sprite_label(sprite, stype, species_name, item_name)
        quests.append(OrderedDict([
            ("questNumber", i + 1), ("questId", i),
            ("name", decode(rom, name)), ("description", decode(rom, desc, newline=newline)),
            ("completedDescription", decode(rom, done, newline=newline)),
            ("location", decode(rom, location_offset)),
            ("spriteType", kind), ("sprite", label), ("spriteId", sprite),
            ("subquests", nsub),
        ]))
        if subquests_pointer and nsub:
            for j in range(nsub):
                subquest_offset = rom.off(subquests_pointer) + SUB_QUEST_SIZE * j
                skind, slabel = sprite_label(rom.u16(subquest_offset + SUB_QUEST_SPRITE),
                                             rom.data[subquest_offset + SUB_QUEST_SPRITE_TYPE], species_name, item_name)
                text_at = lambda field: (decode(rom, rom.off(rom.u32(subquest_offset + field)), newline=newline)
                                         if rom.isptr(rom.u32(subquest_offset + field)) else "")
                subrows.append([i + 1, quests[-1]["name"], j + 1, rom.data[subquest_offset + SUB_QUEST_ID],
                                text_at(SUB_QUEST_NAME), text_at(SUB_QUEST_DESCRIPTION), text_at(SUB_QUEST_MAP),
                                skind, slabel, text_at(SUB_QUEST_LABEL)])

    # --- where the quests are used in map scripts
    opcode = args.questmenu_opcode
    if opcode is None:
        opcode_counts = Counter(ord(match.group("opcode")) for match in MACRO_RE.finditer(rom.data))
        opcode = max(opcode_counts, key=opcode_counts.get) if opcode_counts else QUESTMENU_OPCODE_DEFAULT
    log("questmenu opcode  : 0x%X" % opcode)

    map_groups = args.map_groups
    if map_groups is None: map_groups, _ = find_map_groups(rom)
    rme = args.region_map_entries if args.region_map_entries is not None else find_region_map_entries(rom)
    names = mapsec_names(rom, rme) if rme is not None else []
    maps = list(iter_maps(rom, map_groups))
    log("maps              : %d" % len(maps))

    def route(map_header):
        sec = rom.data[map_header + MAP_HEADER_REGION_MAP_SECTION]
        return names[sec] if sec < len(names) and names[sec] else "MAPSEC_%d" % sec

    entries, _, _ = collect_entries(rom, maps)
    native_args = learn_native_args(rom, sorted({entry.script for entry in entries}))
    walker, cache, reached = Walker(rom, native_args), {}, set()
    events = []
    for script, (map_group, map_num, map_header), x, y, kind, event_offset in entries:
        if script not in cache:
            cache[script] = walker.walk(script).visited
        visited = cache[script]
        reached |= visited
        for pc in sorted(visited):
            if rom.data[pc] != opcode: continue
            case, quest_index = command_args(rom, pc, "BB")
            if case not in QUEST_CASES or case in (QUEST_CASE_OPEN_MENU, QUEST_CASE_BUFFER_NAME) or quest_index >= quest_count:
                continue
            events.append(QuestEvent(quest_index + 1, quests[quest_index]["name"], QUEST_CASES.get(case, "case%d" % case),
                                     route(map_header), "%d.%d" % (map_group, map_num), x, y, kind, "0x%X" % (pc + ROM_BASE)))

    # startquest/completequest macros the walker never reached (unused/dynamic scripts)
    anchors = sorted((script, map_info) for script, map_info, *_ in entries)
    keys = [address for address, _ in anchors]
    for match in MACRO_RE.finditer(rom.data):
        pc = match.start() + MACRO_QUESTMENU_AT
        if ord(match.group("opcode")) != opcode or pc in reached: continue
        quest_index = ord(match.group("quest"))
        if quest_index >= quest_count: continue
        k = bisect.bisect_right(keys, pc) - 1
        if k < 0 or pc - keys[k] > MAX_SCRIPT_DISTANCE:
            route_name, mid = "unknown", ""
        else:
            _, anchor_map = anchors[k]
            route_name, mid = route(anchor_map.header), "%d.%d" % (anchor_map.group, anchor_map.num)
        events.append(QuestEvent(quest_index + 1, quests[quest_index]["name"], QUEST_CASES[ord(match.group("case"))] + "?",
                                 route_name, mid, "", "", "unreached", "0x%X" % (pc + ROM_BASE)))

    seen, uniq = set(), []
    for event in events:
        if tuple(event) not in seen: seen.add(tuple(event)); uniq.append(event)
    events = sorted(uniq, key=lambda event: (event.quest_number, ACTION_ORDER.get(event.action.rstrip("?"), len(ACTION_ORDER)),
                                             event.map_id, event.script_address))

    # summarise into the quest rows
    def where(quest_number, actions):
        places = OrderedDict()
        for event in events:
            if event.quest_number == quest_number and event.action in actions:
                places["%s (%s)" % (event.route, event.map_id) if event.map_id else event.route] = True
        return "; ".join(places)
    for quest_row in quests:
        quest_number = quest_row["questNumber"]
        quest_row["unlockedAt"] = where(quest_number, {"unlock"})
        quest_row["startedAt"] = where(quest_number, {"start", "start?"})
        quest_row["rewardAt"] = where(quest_number, {"reward"})
        quest_row["completedAt"] = where(quest_number, {"complete", "complete?"})

    # --- write
    out = os.path.abspath(args.output)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w", newline="", encoding="utf-8") as csv_file:
        writer = csv.writer(csv_file); writer.writerow(list(quests[0].keys()))
        for quest_row in quests: writer.writerow(list(quest_row.values()))
    ev_path = os.path.join(os.path.dirname(out), "quest_events.csv")
    with open(ev_path, "w", newline="", encoding="utf-8") as csv_file:
        writer = csv.writer(csv_file)
        writer.writerow(QUEST_EVENT_COLUMNS)
        writer.writerows(events)
    log("wrote %d quests -> %s" % (len(quests), out))
    log("wrote %d quest script events -> %s  %s" % (len(events), ev_path, dict(Counter(event.action for event in events))))
    if subrows:
        subquests_path = os.path.join(os.path.dirname(out), "subquests.csv")
        with open(subquests_path, "w", newline="", encoding="utf-8") as csv_file:
            writer = csv.writer(csv_file)
            writer.writerow(["questNumber", "questName", "subquestNumber", "subquestId", "name", "description",
                        "location", "spriteType", "sprite", "label"])
            writer.writerows(subrows)
        log("wrote %d subquests -> %s" % (len(subrows), subquests_path))
    else:
        log("no subquests defined")


if __name__ == "__main__":
    main()
