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
from collections import defaultdict, Counter, OrderedDict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from extract_encounters import Rom, ROM_BASE, find_species, find_map_groups, find_region_map_entries, mapsec_names
from extract_items import (CMD_LEN, END_CMDS, CREATEMON, find_items, iter_maps, collect_entries,
                           learn_native_args, cmd_len, native_len)
from extract_quests import decode, find_quest_table, SIDE_QUEST_SIZE, EXPANSION_GFX_NAMES, OBJ_EVENT_MON

MAX_PATHS = 250          # per script
MAX_STEPS = 4000         # instructions per path
TEMP_VARS = set(range(0x4000, 0x4010)) | set(range(0x8000, 0x8020))
TEMP_FLAGS = set(range(0x00, 0x20))
VAR_RESULT, VAR_8000 = 0x800D, 0x8000
MSGBOX = {2, 3, 4, 5, 6}
TIMES = ["in the morning", "during the day", "in the evening", "at night"]
COND_FN = {0: lambda a, b: a < b, 1: lambda a, b: a == b, 2: lambda a, b: a > b,
           3: lambda a, b: a <= b, 4: lambda a, b: a >= b, 5: lambda a, b: a != b}
COND_TXT = {0: "<", 1: "==", 2: ">", 3: "<=", 4: ">=", 5: "!="}
GENERIC_SPRITES = {"BOY", "GIRL", "LITTLE_BOY", "LITTLE_GIRL", "RICH_BOY", "WOMAN", "FAT_MAN", "POKEFAN",
                   "MAN", "EXPERT", "COOK", "OLD_MAN", "OLD_WOMAN", "CAMPER", "PICNICKER", "YOUNGSTER",
                   "BUG_CATCHER", "PSYCHIC", "SCHOOL_KID", "MANIAC", "HEX_MANIAC", "SWIMMER", "BLACK_BELT",
                   "BEAUTY", "SCIENTIST", "LASS", "GENTLEMAN", "SAILOR", "FISHERMAN", "RUNNING_TRIATHLETE",
                   "TUBER", "HIKER", "CYCLING_TRIATHLETE", "NURSE", "REPORTER", "BARD", "ARTIST", "CAMERAMAN",
                   "TWIN", "NINJA_BOY", "MART_EMPLOYEE", "LINK_RECEPTIONIST", "GAMEBOY_KID", "TUBER_M_SWIMMING",
                   "DEVON_EMPLOYEE", "MOM", "QUINTY_PLUMP"}
RECEIPT_RE = re.compile(r"^(?:\(?)(?:You(?:'ve| have)? (?:just )?(?:earned|received|obtained)|Obtained|You registered)"
                        r"\s+(?:the |a |an )?(.+?)[.!)]*$")


# ------------------------------------------------------------------ helpers --
def clean_text(s):
    s = re.sub(r"(?:… ?)+", " ", s)
    s = re.sub(r"\s*\.\.\.\s*\.\.\.\s*", "... ", s)
    return re.sub(r"\s{2,}", " ", s).strip()


def shorten(s, n=None):
    """Clean up dialogue for output. Text is never cut: n is ignored unless given explicitly."""
    s = clean_text(s)
    return s if n is None or len(s) <= n else s[:n].rsplit(" ", 1)[0] + "…"


def find_multichoice_table(rom):
    """gMultichoiceLists: {const struct MenuAction *list; u8 count;} (8 bytes)."""
    def ok(o):
        p, n = rom.u32(o), rom.d[o + 4]
        if not rom.isptr(p) or p & 3 or not (1 <= n <= 20) or rom.d[o + 5:o + 8] != b"\0\0\0": return False
        q = rom.off(p)
        for i in range(n):
            t = rom.u32(q + 8 * i)
            if not rom.isptr(t) or 0xFF not in rom.d[rom.off(t):rom.off(t) + 60]: return False
        return True
    o, L = 0, rom.L - 8 * 64
    while o < L:
        if ok(o):
            k = 0
            while ok(o + 8 * k): k += 1
            if k >= 64: return o
            o += 8 * max(k, 1)
        else:
            o += 4
    return None


def find_trainer_names(rom, pairs):
    """pairs: [(trainerId, speakerName)]. Trainer names are stored inline in gTrainers;
    find (base, stride) that puts several known speaker names at their trainer ids."""
    from extract_encounters import CHARMAP
    inv = {v: k for k, v in CHARMAP.items() if len(v) == 1}
    occ = {}
    for tid, name in set(pairs):
        try: enc = bytes(inv[c] for c in name) + b"\xff"
        except KeyError: continue
        occ[(tid, name)] = [m.start() for m in re.finditer(re.escape(enc), rom.d)][:40]
    votes = Counter()
    items = [(k[0], o) for k, v in occ.items() for o in v]
    keys = list(occ.items())
    for i in range(len(keys)):
        for j in range(i + 1, len(keys)):
            (t1, _), o1s = keys[i]
            (t2, _), o2s = keys[j]
            if t1 == t2: continue
            for o1 in o1s:
                for o2 in o2s:
                    if (o2 - o1) % (t2 - t1): continue
                    s = (o2 - o1) // (t2 - t1)
                    if 16 <= s <= 256: votes[(o1 - t1 * s, s)] += 1
    if not votes: return None
    (base, stride), v = votes.most_common(1)[0]
    if v < 3: return None
    return lambda t: rom.text(base + stride * t, 13) if 0 <= base + stride * t < rom.L else ""


def range_tiles(tiles):
    """[(x, y)] -> '9,13-15' style text."""
    tiles = sorted(set(tiles))
    if len(tiles) == 1: return "%s,%s" % tiles[0]
    xs, ys = {t[0] for t in tiles}, {t[1] for t in tiles}
    if len(xs) == 1: return "%s,%s–%s" % (tiles[0][0], min(ys), max(ys))
    if len(ys) == 1: return "%s–%s,%s" % (min(xs), max(xs), tiles[0][1])
    return "%s,%s (+%d tiles)" % (tiles[0][0], tiles[0][1], len(tiles) - 1)


# ---------------------------------------------------------- symbolic paths --
class Path:
    __slots__ = ("pc", "stack", "env", "cons", "flags", "src", "cmp", "conds", "effects", "speaker",
                 "regs", "seen", "steps", "end", "last_speaker", "pos_forks")

    def fork(self):
        p = Path.__new__(Path)
        p.pc, p.stack, p.env, p.flags = self.pc, list(self.stack), dict(self.env), dict(self.flags)
        p.cons = {k: list(v) for k, v in self.cons.items()}
        p.src, p.cmp, p.conds, p.effects = dict(self.src), self.cmp, list(self.conds), list(self.effects)
        p.speaker, p.regs, p.seen, p.steps, p.end = self.speaker, dict(self.regs), set(self.seen), self.steps, self.end
        p.last_speaker, p.pos_forks = self.last_speaker, self.pos_forks
        return p


def feasible(cons):
    cands = {0, 1, 0xFFFF}
    for op, v in cons:
        cands |= {v - 1, v, v + 1}
    return any(all(COND_FN[op](x, v) for op, v in cons) for x in cands if 0 <= x <= 0xFFFF)


class Machine:
    def __init__(self, rom, natives, ctx):
        self.rom, self.natives, self.ctx = rom, natives, ctx

    def run(self, start, entry_cond=None):
        p = Path()
        p.pc, p.stack, p.env, p.cons, p.flags, p.src = start, [], {}, {}, {}, {}
        p.cmp, p.conds, p.effects, p.speaker, p.regs, p.seen, p.steps, p.end = None, [], [], None, {}, set(), 0, None
        p.last_speaker, p.pos_forks = None, 0
        if entry_cond:
            v, val = entry_cond
            p.env[v] = val; p.cons[v] = [(1, val)]
            p.conds.append(("var", v, 1, val, None))
        todo, done = [p], []
        while todo and len(done) < MAX_PATHS:
            p = todo.pop()
            while p.end is None:
                if p.steps > MAX_STEPS or not (0 <= p.pc < self.rom.L):
                    p.end = "limit"; break
                key = (p.pc, tuple(p.stack))
                if key in p.seen:
                    p.end = "loop"; break
                p.seen.add(key); p.steps += 1
                fork = self.step(p)
                if fork is not None: todo.append(fork)
            done.append(p)
        return done

    # ---- helpers
    def set_var(self, p, v, val):
        p.env[v] = val; p.cons.pop(v, None); p.src.pop(v, None)

    def new_result(self, p, var, desc):
        p.env.pop(var, None); p.cons.pop(var, None); p.src[var] = desc

    def branch(self, p, cond, target, is_call):
        """returns fork (or None); p continues with the not-taken side."""
        c = p.cmp
        outcome = None
        if c and c[0] == "var" and c[1] in p.env:
            outcome = COND_FN[cond](p.env[c[1]], c[2])
        elif c and c[0] == "varvar" and c[1] in p.env and c[2] in p.env:
            outcome = COND_FN[cond](p.env[c[1]], p.env[c[2]])
        elif c and c[0] == "flag" and c[1] in p.flags:
            r = 1 if p.flags[c[1]] else 0
            outcome = COND_FN[cond](r, 1)
        if outcome is not None:
            if outcome: self.jump(p, target, is_call)
            return None
        # branches on the player's position only pick a walking route. Follow both sides for the
        # first two of them in a path, after that only the jump (avoids 2^n identical paths)
        if (c and c[0] == "varvar") or (c and c[0] == "var" and p.src.get(c[1]) == ("position",)):
            p.pos_forks += 1
            if p.pos_forks > 2:
                self.jump(p, target, is_call); return None
            taken = p.fork(); self.jump(taken, target, is_call)
            return taken
        taken = p.fork()
        ok_t = self.assume(taken, cond, True)
        ok_n = self.assume(p, cond, False)
        if ok_t: self.jump(taken, target, is_call)
        if not ok_n:
            if ok_t:   # only the taken side is possible: continue with it
                return self._replace(p, taken)
            p.end = "infeasible"
        return taken if ok_t else None

    def _replace(self, p, q):
        for s in Path.__slots__: setattr(p, s, getattr(q, s))
        return None

    def assume(self, p, cond, truth):
        c = p.cmp
        if c is None: return True
        if c[0] == "flag":
            # checkflag: comparison result 1 when set; cond 1/4 -> set, 0/5 -> clear
            want = {1: True, 4: True, 0: False, 5: False}.get(cond)
            if want is None: return truth if cond == 3 else not truth if cond == 2 else True
            val = want if truth else not want
            if c[1] in p.flags and p.flags[c[1]] != val: return False
            p.flags[c[1]] = val
            p.conds.append(("flag", c[1], val))
            return True
        if c[0] == "var":
            v, val = c[1], c[2]
            op = cond if truth else {0: 4, 1: 5, 2: 3, 3: 2, 4: 0, 5: 1}[cond]
            cons = p.cons.setdefault(v, []) + [(op, val)]
            if not feasible(cons): return False
            p.cons[v] = cons
            if op == 1: p.env[v] = val
            p.conds.append(("var", v, op, val, p.src.get(v)))
            return True
        return True   # var-vs-var (positions): no constraint

    def jump(self, p, target, is_call):
        if not self.rom.isptr(target):
            p.end = "badptr"; return
        if is_call: p.stack.append(p.pc)
        p.pc = self.rom.off(target)

    def say(self, p, text_ptr, kind="say"):
        if self.rom.isptr(text_ptr):
            t = decode(self.rom, self.rom.off(text_ptr), maxlen=4000)
            if "{STR_VAR_1}' is now {STR_VAR_2}" in t: return     # startquest/completequest banner
            p.effects.append((kind, p.speaker, t))

    # ---- one instruction; p.pc is advanced (or jumped). Returns a forked path or None.
    def step(self, p):
        r, pc, c = self.rom, p.pc, self.ctx
        op = r.d[pc]
        ln = cmd_len(r, pc, self.natives)
        if not ln:
            p.end = "unknown op 0x%02X" % op; return None
        u8 = lambda k: r.d[pc + k]
        u16 = lambda k: r.u16(pc + k)
        u32 = lambda k: r.u32(pc + k)
        p.pc = pc + ln
        if op == 0x02:
            p.end = "end"
        elif op == 0x03:
            if p.stack: p.pc = p.stack.pop()
            else: p.end = "end"
        elif op == 0x04: self.jump(p, u32(1), True)
        elif op == 0x05: self.jump(p, u32(1), False)
        elif op in (0x06, 0x07): return self.branch(p, u8(1), u32(2), op == 0x07)
        elif op == 0x0F and u8(1) == 0: p.regs["text"] = u32(2)
        elif op in (0x08, 0x09):
            std = u8(1)
            if std in MSGBOX and "text" in p.regs:
                t = p.regs.pop("text")
                self.say(p, t)
                if std == 5:
                    self.new_result(p, VAR_RESULT, ("yesno",))
            elif std in (0, 1) and 0x8000 in p.regs:
                item, qty = p.regs[0x8000], p.regs.get(0x8001, 1)
                if item < 0x4000:
                    p.effects.append(("give_item" if std == 0 else "find_item", item, qty if qty < 0x4000 else 1))
                self.new_result(p, VAR_RESULT, None)
            if op == 0x08: p.end = "end"
        elif op == 0x67: self.say(p, u32(1))
        elif op == 0xE5:
            p.speaker = decode(r, r.off(u32(1))) if r.isptr(u32(1)) else None
            if p.speaker and p.speaker != "???": p.last_speaker = p.speaker
        elif op == 0xE6: p.speaker = None
        elif op == 0xDF: self.say(p, u32(1), "phone")
        elif op in (0x16, 0x1A):
            v, val = u16(1), u16(3)
            if op == 0x1A and val >= 0x4000:
                if val in p.env: self.set_var(p, v, p.env[val])
                else: p.env.pop(v, None); p.cons.pop(v, None)
                if val in p.src: p.src[v] = p.src[val]
            else:
                self.set_var(p, v, val)
                if v in (0x8000, 0x8001): p.regs[v] = val
                if v not in TEMP_VARS: p.effects.append(("setvar", v, val))
        elif op in (0x17, 0x18):
            v, val = u16(1), u16(3)
            if v in p.env:
                self.set_var(p, v, (p.env[v] + (val if op == 0x17 else -val)) & 0xFFFF)
            else:
                p.cons.pop(v, None)
            if v not in TEMP_VARS: p.effects.append(("addvar", v, val if op == 0x17 else -val))
        elif op == 0x19:
            d, s = u16(1), u16(3)
            if s in p.env: self.set_var(p, d, p.env[s])
            else: p.env.pop(d, None); p.cons[d] = list(p.cons.get(s, []))
            if s in p.src: p.src[d] = p.src[s]
            else: p.src.pop(d, None)
        elif op == 0x21: p.cmp = ("var", u16(1), u16(3))
        elif op == 0x22: p.cmp = ("varvar", u16(1), u16(3))
        elif op == 0x2B: p.cmp = ("flag", u16(1))
        elif op in (0x29, 0x2A):
            f = u16(1); p.flags[f] = op == 0x29
            if f not in TEMP_FLAGS: p.effects.append(("flag", f, op == 0x29))
        elif op == 0x60: p.cmp = ("flag", ("trainer", u16(1)))
        elif op == 0x25: p.effects.append(("special", u16(1)))
        elif op == 0x26: self.new_result(p, u16(1), ("special", u16(3)))
        elif op in (0x39, 0x3A, 0x3B, 0x3C, 0x3D):
            p.effects.append(("warp", (u8(1), u8(2))))
        elif op == 0x42:
            for k in (1, 3): self.new_result(p, u16(k), ("position",))
        elif op == 0x44:
            p.effects.append(("give_item", u16(1), u16(3))); self.new_result(p, VAR_RESULT, None)
        elif op == 0x45: p.effects.append(("take_item", u16(1), u16(3)))
        elif op == 0x47: self.new_result(p, VAR_RESULT, ("has_item", u16(1), u16(3)))
        elif op == 0x5C:
            p.effects.append(("trainer", u16(3), p.speaker or p.last_speaker))
            if r.isptr(u32(13)) and abs(r.off(u32(13)) - pc) < 0x2000: self.jump(p, u32(13), False)
        elif op == 0x6E: self.new_result(p, VAR_RESULT, ("yesno",))
        elif op in (0x6F, 0x70, 0x71): self.new_result(p, VAR_RESULT, ("menu", u8(3)))
        elif op == 0x79: p.effects.append(("give_mon", u16(1), u8(3))); self.new_result(p, VAR_RESULT, None)
        elif op == 0x7A: p.effects.append(("give_egg", u16(1)))
        elif op == 0x86: p.effects.append(("shop",))
        elif op == 0x90: p.effects.append(("money", u32(1)))
        elif op == 0x91: p.effects.append(("money", -u32(1)))
        elif op == 0x92: self.new_result(p, VAR_RESULT, ("money", u32(1)))
        elif op == 0xB6: p.effects.append(("wild", u16(1), u8(3)))
        elif op == 0xE7:
            case, q = u8(1), u8(2)
            if 1 <= case <= 4: p.effects.append(("quest", case, q))
            elif 5 <= case <= 9: self.new_result(p, VAR_RESULT, ("questcheck", case, q))
        elif op == 0x23:
            t = u32(1); kind = c.native_kind.get(t)
            if self.natives.get(t) == CREATEMON:
                if u8(5) == 0: p.effects.append(("give_mon", u16(7), u16(9)))
                self.new_result(p, VAR_RESULT, None)
            elif kind == "time": self.new_result(p, VAR_8000, ("time",))
            elif kind == "species": self.new_result(p, VAR_RESULT, ("species", u16(5)))
            elif kind == "dex": self.new_result(p, VAR_RESULT, ("dex", u16(5), u16(7)))
            elif kind == "objxy":
                for k in (9, 11): self.new_result(p, u16(k), ("position",))
        return None


# ------------------------------------------------------------- the game --
class Game:
    def __init__(self, rom, here):
        self.rom = rom
        sb, sst, sno, _, self.scount = find_species(rom)
        self.species = lambda i: rom.text(sb + sst * i + sno, 20) if 0 < i < self.scount else "species #%d" % i
        self.item = find_items(rom)[3]
        self.qt, self.qn = find_quest_table(rom)
        self.qnames = [decode(rom, rom.off(rom.u32(self.qt + SIDE_QUEST_SIZE * i))) for i in range(self.qn)]
        mg = find_map_groups(rom)[0]
        rme = find_region_map_entries(rom)
        secs = mapsec_names(rom, rme) if rme is not None else []
        self.maps = list(iter_maps(rom, mg))
        self.mapname_ = {}
        for g, n, mh in self.maps:
            sec = rom.d[mh + 0x14]
            self.mapname_[(g, n)] = "%s (%d.%d)" % (secs[sec] if sec < len(secs) else "MAPSEC_%d" % sec, g, n)
        self.entries, _, _ = collect_entries(rom, self.maps)
        self.natives = learn_native_args(rom, sorted({e[0] for e in self.entries}))
        self.native_kind = self.classify_natives()
        mt = find_multichoice_table(rom)
        self.menu = lambda mid, i: (decode(rom, rom.off(rom.u32(rom.off(rom.u32(mt + 8 * mid)) + 8 * i)))
                                    if mt is not None and i < rom.d[mt + 8 * mid + 4] else "option %d" % (i + 1))
        self.items_csv = self.load_csv(os.path.join(here, "output", "items.csv"))
        self.enc_csv = self.load_csv(os.path.join(here, "output", "encounters.csv"))

    def mapname(self, m): return self.mapname_.get(tuple(m[:2]), "map %d.%d" % tuple(m[:2]))

    @staticmethod
    def load_csv(path):
        if not os.path.exists(path): return []
        with open(path, encoding="utf-8") as f: return list(csv.DictReader(f))

    def classify_natives(self):
        """Recognise a few expansion natives by how scripts use them."""
        from extract_items import Walker
        rom, votes = self.rom, defaultdict(Counter)
        w = Walker(rom, self.natives)
        for s in sorted({e[0] for e in self.entries}):
            for pc in w.walk(s)[3]:
                if rom.d[pc] != 0x23: continue
                t, n = rom.u32(pc + 1), native_len(rom, pc, self.natives)
                nx = pc + 5 + n
                cmpv = rom.u16(nx + 1) if rom.d[nx] == 0x21 else None
                val = rom.u16(nx + 3) if cmpv is not None else None
                if n == 0 and cmpv == VAR_8000 and val <= 3: votes[t]["time"] += 1
                elif n == 2 and cmpv == VAR_RESULT and 0 < rom.u16(pc + 5) < self.scount: votes[t]["species"] += 1
                elif n == 4 and cmpv == VAR_RESULT and 0 < rom.u16(pc + 5) < self.scount and rom.u16(pc + 7) <= 1:
                    votes[t]["dex"] += 1
                elif n == 8 and all(0x4000 <= rom.u16(pc + 5 + k) < 0x4020 for k in (4, 6)): votes[t]["objxy"] += 1
                else: votes[t]["other"] += 1
        out = {}
        for t, c in votes.items():
            k, v = c.most_common(1)[0]
            if k != "other" and v * 2 > sum(c.values()) - c["other"] and (k != "objxy" or c["other"] == 0):
                out[t] = k
        return out


def entry_conditions(rom, entries):
    """Triggers and frame/warp-into map scripts only run when var == value."""
    out = {}
    for sc, (g, n, mh), x, y, kind, eo in entries:
        if kind == "trigger":
            v, val = rom.u16(eo + 6), rom.u16(eo + 8)
            if v: out.setdefault(sc, (v, val))
    seen = set()
    for sc, (g, n, mh), x, y, kind, eo in entries:
        if kind != "mapscript" or mh in seen: continue
        seen.add(mh)
        ms = rom.u32(mh + 8)
        if not rom.isptr(ms): continue
        ms = rom.off(ms)
        for k in range(16):
            t = rom.d[ms + 5 * k]
            if t == 0: break
            ptr = rom.u32(ms + 5 * k + 1)
            if not rom.isptr(ptr): break
            if t in (2, 4):
                tb = rom.off(ptr)
                for j in range(32):
                    v = rom.u16(tb + 8 * j)
                    if v == 0: break
                    s2 = rom.u32(tb + 8 * j + 4)
                    if rom.isptr(s2): out.setdefault(rom.off(s2), (v, rom.u16(tb + 8 * j + 2)))
    return out


# ------------------------------------------------------------- analysis --
class Analysis:
    def __init__(self, game, bulk=15, max_flag_users=8, max_var_users=15):
        self.g, self.bulk = game, bulk
        g = game
        self.machine = Machine(g.rom, g.natives, g)
        self.where = defaultdict(list)
        for s, m, x, y, kind, eo in g.entries:
            self.where[s].append((m, x, y, kind, eo))
        self.entry_cond = entry_conditions(g.rom, g.entries)
        self.paths = {}
        for s in self.where:
            self.paths[s] = self.machine.run(s, self.entry_cond.get(s))
        # who reads / writes what
        self.writers_f, self.writers_v = defaultdict(set), defaultdict(set)
        self.users_f, self.users_v = defaultdict(set), defaultdict(set)
        for s, ps in self.paths.items():
            for p in ps:
                for e in p.effects:
                    if e[0] == "flag": self.writers_f[e[1]].add(s); self.users_f[e[1]].add(s)
                    elif e[0] in ("setvar", "addvar"): self.writers_v[e[1]].add(s); self.users_v[e[1]].add(s)
                for cnd in p.conds:
                    if cnd[0] == "flag" and not isinstance(cnd[1], tuple): self.users_f[cnd[1]].add(s)
                    elif cnd[0] == "var": self.users_v[cnd[1]].add(s)
        self.max_flag_users, self.max_var_users = max_flag_users, max_var_users
        self.story_var = self.find_story_var()
        self.trainer_name = find_trainer_names(g.rom, [(e[1], e[2]) for ps in self.paths.values() for p in ps
                                                         for e in p.effects if e[0] == "trainer" and e[2]])
        self.story_paths = defaultdict(list)
        if self.story_var is not None:
            for s, ps in self.paths.items():
                for p in ps:
                    v = self.final_value(p, self.story_var)
                    if v is not None: self.story_paths[v].append((s, p))
        # quest completion / story milestones that set a flag or var (for "after ..." conditions)
        self.flag_from_quest, self.var_from_quest = {}, {}
        for s, ps in self.paths.items():
            for p in ps:
                done = [e[2] for e in p.effects if e[0] == "quest" and e[1] == 4]
                for q in done:
                    for e in p.effects:
                        if e[0] == "flag" and e[2]: self.flag_from_quest.setdefault(e[1], q)
                        if e[0] == "setvar": self.var_from_quest.setdefault((e[1], e[2]), q)

    # ---- small queries
    def final_value(self, p, var):
        val = None
        for e in p.effects:
            if e[0] == "setvar" and e[1] == var: val = e[2]
        return val

    def path_writes(self, p):
        return {("f", e[1]) for e in p.effects if e[0] == "flag"} | \
               {("v", e[1]) for e in p.effects if e[0] in ("setvar", "addvar")}

    def is_bulk(self, p):
        return len(self.path_writes(p)) > self.bulk

    def find_story_var(self):
        vals = defaultdict(set)
        for ps in self.paths.values():
            for p in ps:
                for e in p.effects:
                    if e[0] == "setvar" and e[1] not in TEMP_VARS: vals[e[1]].add(e[2])
        if not vals: return None
        v, s = max(vals.items(), key=lambda kv: len(kv[1]))
        return v if len(s) >= 15 else None

    def quest_paths_all(self, q):
        """every path of every script that starts or completes quest q"""
        scripts = {s for s, ps in self.paths.items() for p in ps
                   if any(e[0] == "quest" and e[2] == q for e in p.effects)}
        return [p for s in scripts for p in self.paths[s]]

    def quest_paths(self, q, case):
        return [(s, p) for s, ps in self.paths.items() for p in ps
                if any(e[0] == "quest" and e[1] == case and e[2] == q for e in p.effects)]

    # ---- the steps of one quest
    def quest_steps(self, q):
        starts = self.quest_paths(q, 2) + self.quest_paths(q, 1)
        dones = self.quest_paths(q, 4)
        core = starts + dones
        state_f, state_v = set(), set()
        for s, p in core:
            if self.is_bulk(p): continue
            for e in p.effects:
                if e[0] == "flag" and len(self.users_f[e[1]]) <= self.max_flag_users: state_f.add(e[1])
                if e[0] in ("setvar", "addvar") and e[1] != self.story_var and \
                        len(self.users_v[e[1]]) <= self.max_var_users: state_v.add(e[1])
            for cnd in p.conds:
                if cnd[0] == "var" and cnd[1] not in TEMP_VARS and cnd[1] != self.story_var and \
                        len(self.users_v[cnd[1]]) <= self.max_var_users: state_v.add(cnd[1])
                if cnd[0] == "flag" and not isinstance(cnd[1], tuple) and cnd[1] not in TEMP_FLAGS and \
                        len(self.users_f[cnd[1]]) <= self.max_flag_users: state_f.add(cnd[1])
        # NPCs that start/complete the quest: their visibility flags
        npc_flags = set()
        for s, p in core:
            for m, x, y, kind, eo in self.where[s]:
                if kind == "object" and self.g.rom.u16(eo + 20) not in TEMP_FLAGS:
                    npc_flags.add(self.g.rom.u16(eo + 20))
        steps = []
        seen_paths = set()
        def add(s, p, role):
            if id(p) in seen_paths: return None
            seen_paths.add(id(p)); st = Step(self, q, s, p, role, state_f, state_v); steps.append(st)
            return st
        for s, p in starts: add(s, p, "start")
        for s, p in dones: add(s, p, "done")
        # other paths that change the quest state in a way some quest step is waiting for
        cands = []
        for s, ps in self.paths.items():
            for p in ps:
                if id(p) in seen_paths or self.is_bulk(p): continue
                w = self.path_writes(p)
                if any(k == "f" and f in state_f for k, f in w) or any(k == "v" and v in state_v for k, v in w):
                    cands.append((s, p, Step(self, q, s, p, "step", state_f, state_v)))
                elif any(e[0] == "flag" and not e[2] and e[1] in npc_flags and self.only_hidden_by_setup(e[1], core, p)
                         for e in p.effects):
                    add(s, p, "unlock")
        if not dones:
            # nothing completes the quest: show what the quest giver does once you're done
            for s in {s for s, p in starts}:
                for p in self.paths[s]:
                    if id(p) not in seen_paths and not self.is_bulk(p) and \
                            any(e[0] in ("setvar", "special") and (e[0] != "setvar" or e[1] not in TEMP_VARS)
                                for e in p.effects) and len(p.conds) > 2:
                        add(s, p, "final")
        for _ in range(6):
            reqs = [rq for st in steps for rq in st.requires]
            added = False
            for s, p, st in cands:
                if id(p) in seen_paths: continue
                if any(satisfies(pv, rq) for pv in st.provides for rq in reqs):
                    seen_paths.add(id(p)); steps.append(st); added = True
            if not added: break
        # story events between start and completion
        sv = self.story_var
        if sv is not None:
            a = [self.final_value(p, sv) for s, p in starts if self.final_value(p, sv) is not None]
            b = [self.final_value(p, sv) for s, p in dones if self.final_value(p, sv) is not None]
            if a and b and min(b) - max(a) > 1:
                for v in range(max(a) + 1, min(b)):
                    for s, p in self.pick_story(v):
                        if id(p) not in seen_paths:
                            seen_paths.add(id(p)); steps.append(Step(self, q, s, p, "story", state_f, state_v, story=v))
        if sv is not None and a and b:
            lo, hi = max(a), min(b)
            keep = []
            for st in steps:
                pos = st.story_pos()
                if st.role in ("step",) and pos is not None and not (lo <= pos <= hi): continue
                keep.append(st)
            steps = keep
        return order_steps(self, steps, state_v)

    def story_pos(self, p):
        if self.story_var is None: return None
        v = self.final_value(p, self.story_var)
        if v is not None: return v
        need = None
        for cnd in p.conds:
            if cnd[0] == "var" and cnd[1] == self.story_var and cnd[2] in (1, 2, 4):
                x = cnd[3] + (1 if cnd[2] == 2 else 0)
                need = x if need is None else max(need, x)
        return need

    def only_hidden_by_setup(self, f, core, clearer):
        """Is clearing flag f a real 'unlock'? Only if everything else that hides the NPC is
        new-game setup or happens earlier in the story than the clearing."""
        own = {s for s, p in core}
        cpos = self.story_pos(clearer)
        for s, ps in self.paths.items():
            if s in own: continue
            for p in ps:
                if not self.is_bulk(p) and any(e[0] == "flag" and e[1] == f and e[2] for e in p.effects):
                    spos = self.story_pos(p)
                    if cpos is None: return False
                    if spos is not None and spos >= cpos: return False   # (setters we can't place are ignored)
        return True

    def pick_story(self, v):
        """The most informative path(s) that move the story to v (one per distinct event)."""
        cands = self.story_paths.get(v, [])
        best = {}
        for s, p in cands:
            if self.is_bulk(p) and not any(e[0] == "quest" for e in p.effects):
                continue
            score = sum(1 for e in p.effects if e[0] != "say") * 3 + len([e for e in p.effects if e[0] == "say"])
            k = s
            if k not in best or score > best[k][0]: best[k] = (score, s, p)
        if not best:
            for s, p in cands[:1]: return [(s, p)]
            return []
        # several scripts can set the same value (e.g. two trigger rows): keep the best one per map
        per_map = {}
        for score, s, p in best.values():
            m = self.where[s][0][0]
            if m not in per_map or score > per_map[m][0]: per_map[m] = (score, s, p)
        return [(s, p) for _, s, p in sorted(per_map.values(), key=lambda t: -t[0])][:2]


# ---------------------------------------------------------------- steps --
class Step:
    def __init__(self, an, q, script, path, role, state_f, state_v, story=None):
        self.an, self.q, self.script, self.p, self.role = an, q, script, path, role
        self.state_f, self.state_v, self.story = state_f, state_v, story
        g = an.g
        self.provides, self.requires = set(), []
        for e in path.effects:
            if e[0] == "flag": self.provides.add(("flag", e[1], e[2]))
            if e[0] in ("give_item", "find_item"): self.provides.add(("item", e[1]))
        for v in state_v:
            val = an.final_value(path, v)
            if val is not None: self.provides.add(("var", v, val))
        for m, x, y, kind, eo in an.where[script]:
            if kind == "object":
                vf = g.rom.u16(eo + 20)
                if vf and vf not in TEMP_FLAGS: self.requires.append(("flag", vf, False))
                break
        # only "positive" requirements order steps: flag must be set, var ==/>/>= n
        # (plus the NPC's own visibility flag being clear, added above)
        for cnd in path.conds:
            if cnd[0] == "flag" and cnd[1] in state_f and cnd[2]: self.requires.append(("flag", cnd[1], True))
            if cnd[0] == "var" and cnd[1] in state_v and (cnd[2] in (1, 2, 4) or (cnd[2] == 5 and cnd[3] == 0)):
                self.requires.append(("var", cnd[1], cnd[2], cnd[3]))
            if cnd[0] == "var" and cnd[4] and cnd[4][0] == "has_item" and \
                    self.positive(cnd): self.requires.append(("item", cnd[4][1]))

    @staticmethod
    def positive(cnd):
        op, val = cnd[2], cnd[3]
        return (op == 1 and val == 1) or (op == 5 and val == 0) or (op in (2, 4) and val >= 0 and COND_FN[op](1, val))

    def has_substance(self):
        show = [e for e in self.p.effects if e[0] not in ("say", "setvar", "addvar", "flag", "special")]
        return bool(show) or any(e[0] == "say" for e in self.p.effects)

    def story_pos(self):
        return self.an.story_pos(self.p)

    def var_rank(self):
        vals = [val for k, v, val in [x for x in self.provides if x[0] == "var"]]
        return min(vals) if vals else 0

    # ---- rendering
    def trigger(self):
        g, an = self.an.g, self.an
        locs = an.where[self.script]
        kinds = Counter(l[3] for l in locs)
        kind = kinds.most_common(1)[0][0]
        bymap = OrderedDict()
        for m, x, y, k, eo in locs:
            if k == kind: bymap.setdefault(m, []).append((x, y, eo))
        first_map = next(iter(bymap))
        def place(m, pts):
            if kind == "mapscript": return g.mapname(m)
            return "%s %s" % (g.mapname(m), range_tiles([(x, y) for x, y, _ in pts]))
        where = " / ".join(place(m, pts) for m, pts in list(bymap.items())[:3])
        if kind == "object":
            eo = bymap[first_map][0][2]
            who = self.who(g.rom.u16(eo + 1))
            if who in ("Poké Ball", "item ball", "fossil"):
                return "Pick up the %s at %s" % (who, where)
            return "Talk to %s at %s" % (who, where)
        if kind == "trigger": return "Walk onto %s" % where
        if kind == "sign": return "Check %s" % where
        return "Go to %s" % where

    def who_default(self):
        locs = self.an.where[self.script]
        for m, x, y, k, eo in locs:
            if k == "object":
                w = self.who(self.an.g.rom.u16(eo + 1))
                return w[4:] if w.startswith("the ") else w
        return "NPC" if not locs or locs[0][3] == "object" else "Text"

    def who(self, gfx):
        g = self.an.g
        sp = next((e[1] for e in self.p.effects if e[0] == "say" and e[1]), None)
        if not sp:
            c = Counter(e[1] for p in self.an.paths[self.script] for e in p.effects if e[0] == "say" and e[1]
                        and e[1] != "???")
            sp = c.most_common(1)[0][0] if c else None
        if gfx & OBJ_EVENT_MON:
            return "the %s" % g.species(gfx & ~(7 << 12))
        name = EXPANSION_GFX_NAMES[gfx] if gfx < len(EXPANSION_GFX_NAMES) else None
        if name == "POKE_BALL": return "Poké Ball"
        if name == "ITEM_BALL": return "item ball"
        if name == "FOSSIL": return "fossil"
        if sp: return sp
        if name:
            base = re.sub(r"_(\d+|M|F)$", "", name)
            if base in GENERIC_SPRITES or name in GENERIC_SPRITES:
                nice = {"LINK_RECEPTIONIST": "receptionist", "MART_EMPLOYEE": "shop clerk",
                        "TUBER_M_SWIMMING": "swimming kid", "DEVON_EMPLOYEE": "employee",
                        "MOM": "woman", "QUINTY_PLUMP": "man"}.get(name, base.lower().replace("_", " "))
                return "the " + nice
        return "the NPC"

    def condition_texts(self):
        g, an, out = self.an.g, self.an, []
        p = self.p
        # time of day: combine all constraints on the time var
        for v, cons in p.cons.items():
            if p.src.get(v) == ("time",):
                ok = [t for t in range(4) if all(COND_FN[op](t, val) for op, val in cons)]
                if 0 < len(ok) < 4:
                    out.append(" or ".join(TIMES[t] for t in ok))
        for cnd in p.conds:
            if cnd[0] == "var":
                v, op, val, src = cnd[1], cnd[2], cnd[3], cnd[4]
                if src is None:
                    if v == an.story_var:
                        t = self.story_text(op, val)
                        if t: out.append(t)
                    elif v not in self.state_v and v not in TEMP_VARS:
                        q = an.var_from_quest.get((v, val)) if op == 1 else None
                        if q is not None and q != self.q: out.append("after finishing quest %d (%s)" % (q + 1, g.qnames[q]))
                    continue
                kind = src[0]
                pos = self.positive(cnd)
                if kind == "yesno": out.append('answer "Yes"' if pos else 'answer "No"')
                elif kind == "has_item" and pos:
                    out.append("have %s%s" % ("%d× " % src[2] if src[2] > 1 else "", g.item(src[1])))
                elif kind == "species" and pos: out.append("have a %s in your party" % g.species(src[1]))
                elif kind == "species": pass
                elif kind == "dex":
                    what = "caught" if src[2] else "seen"
                    out.append(("if you %s %s" if pos else "if you haven't %s %s") % (what, g.species(src[1])))
                elif kind == "menu" and op == 1:
                    out.append('choose "%s"' % g.menu(src[1], val))
                elif kind == "special" and pos: out.append("(game check: special %d passes)" % src[1])
                elif kind == "money" and pos: out.append("have at least ¥%d" % src[1])
            elif cnd[0] == "flag":
                f, val = cnd[1], cnd[2]
                if isinstance(f, tuple) or f in self.state_f or f in TEMP_FLAGS or not val: continue
                q = an.flag_from_quest.get(f)
                if q is not None and q != self.q:
                    out.append("after finishing quest %d (%s)" % (q + 1, g.qnames[q]))
        return list(OrderedDict.fromkeys(out))

    def story_text(self, op, val):
        an = self.an
        need = val + 1 if op == 2 else val if op in (1, 4) else None
        if need is None or need <= 0: return None
        for s, p in an.pick_story(need)[:1]:
            m = an.where[s][0][0]
            return "after the story event in %s (story step %d)" % (an.g.mapname(m), need)
        return "after story step %d" % need

    def action_texts(self):
        g, an, out = self.an.g, self.an, []
        says = [i for i, e in enumerate(self.p.effects) if e[0] == "say" and len(clean_text(e[2])) > 12
                and not (RECEIPT_RE.match(clean_text(e[2])) and "?" not in e[2])]
        quote_at = set(says[:1] + says[-1:])
        default_who = self.who_default()
        for i, e in enumerate(self.p.effects):
            k = e[0]
            if k == "say":
                text = clean_text(e[2])
                m = RECEIPT_RE.match(text) if "?" not in text else None
                if m and len(text) < 90:
                    what = m.group(1).rstrip("!.")
                    if text.startswith("You registered"):
                        out.append("New phone contact: %s" % what); continue
                    if not any(o.startswith("Receive ") and (o[8:].split(" (")[0] in what or what in o) for o in out):
                        out.append("Receive %s" % what)
                elif i in quote_at:
                    if len(says) > 2 and i == says[-1]: out.append("…")
                    out.append('%s: "%s"' % (e[1] or default_who, shorten(text)))
            elif k == "phone":
                t = clean_text(e[2])
                t = re.sub(r"^.*?Beep!\s*", "", t); t = re.sub(r"\s*Click!.*$", "", t)
                out.append('Phone call: "%s"' % shorten(t))
            elif k == "trainer":
                name = (an.trainer_name(e[1]) if an.trainer_name else "") or e[2]
                out.append("Battle %s (trainer #%d)" % (name, e[1]) if name else "Battle trainer #%d" % e[1])
            elif k == "wild": out.append("Battle a wild %s (Lv%d)" % (g.species(e[1]), e[2]))
            elif k in ("give_item", "find_item"):
                out.append("Receive %s%s" % (g.item(e[1]), " ×%d" % e[2] if e[2] > 1 else ""))
            elif k == "take_item": out.append("Hand over %s%s" % (g.item(e[1]), " ×%d" % e[2] if e[2] > 1 else ""))
            elif k == "give_mon": out.append("Receive %s (Lv%d)" % (g.species(e[1]), e[2]))
            elif k == "give_egg": out.append("Receive a %s Egg" % g.species(e[1]))
            elif k == "money": out.append("Receive ¥%d" % e[1] if e[1] > 0 else "Pay ¥%d" % -e[1])
            elif k == "warp": out.append("You're taken to %s" % g.mapname(e[1]))
            elif k == "quest" and e[2] != self.q:
                out.append("%s quest %d (%s)" % ({1: "Unlocks", 2: "Starts", 3: "Readies", 4: "Completes"}[e[1]],
                                                  e[2] + 1, g.qnames[e[2]]))
        return list(OrderedDict.fromkeys(out))

    def needed_items(self):
        out = []
        for cnd in self.p.conds:
            if cnd[0] == "var" and cnd[4] and cnd[4][0] == "has_item" and self.positive(cnd):
                out.append(cnd[4][1])
        return list(OrderedDict.fromkeys(out))

    def needed_species(self):
        return list(OrderedDict.fromkeys(cnd[4][1] for cnd in self.p.conds if cnd[0] == "var" and cnd[4]
                                         and cnd[4][0] == "species" and self.positive(cnd)))

    def key(self):
        return (self.role, self.trigger(), tuple(self.condition_texts()), tuple(self.action_texts()))


def satisfies(prov, req):
    """Does a step that provides `prov` make requirement `req` true?"""
    if req[0] == "flag": return prov[0] == "flag" and prov[1] == req[1] and prov[2] == req[2]
    if req[0] == "item": return prov[0] == "item" and prov[1] == req[1]
    if req[0] == "var":
        if prov[0] != "var" or prov[1] != req[1] or not COND_FN[req[2]](prov[2], req[3]): return False
        return prov[2] != 0      # setting a var back to 0 (its initial value) never moves a quest on
    return False


IMPORTANT = ("trainer", "wild", "give_item", "find_item", "take_item", "give_mon", "give_egg", "money",
             "warp", "quest", "setvar", "addvar", "flag")


def order_steps(an, steps, state_v):
    # 1. merge paths of the same script that do the same things (e.g. "nickname it? yes/no")
    groups = OrderedDict()
    for st in steps:
        k = (st.role, st.script, tuple(e for e in st.p.effects if e[0] in IMPORTANT))
        groups.setdefault(k, []).append(st)
    merged = []
    for members in groups.values():
        st = members[0]
        conds = [c for c in st.condition_texts() if all(c in m.condition_texts() for m in members[1:])]
        st.merged_conds = conds
        for m in members[1:]:
            st.provides |= m.provides
        merged.append(st)
    steps, n = merged, len(merged)
    # 2. dependency edges and levels
    succ = defaultdict(set)
    for i in range(n):
        for j in range(n):
            if i != j and any(satisfies(pv, rq) for pv in steps[i].provides for rq in steps[j].requires):
                succ[i].add(j)
    level = [0] * n
    for _ in range(n):
        changed = False
        for i in range(n):
            for j in succ[i]:
                if level[j] < level[i] + 1 <= n:
                    level[j] = level[i] + 1; changed = True
        if not changed: break
    def reach(src):
        seen, todo = set(), list(src)
        while todo:
            i = todo.pop()
            for j in succ[i]:
                if j not in seen: seen.add(j); todo.append(j)
        return seen
    starts = [i for i in range(n) if steps[i].role == "start"]
    dones = [i for i in range(n) if steps[i].role in ("done", "final")]
    after = reach(dones) - set(dones) - set(starts)
    # steps that lead to a start are prerequisites
    pred = defaultdict(set)
    for i in range(n):
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
    for s_, idx in by_script.items():
        if len(idx) < 2: continue
        useful = [i for i in idx if succ[i] - set(idx)] or idx
        best = min(useful, key=lambda i: (len(steps[i].merged_conds), -len(succ[i])))
        drop |= set(idx) - {best}
    def group(i):
        st = steps[i]
        if st.role == "unlock" or i in pre: return 0
        if st.role == "start": return 1
        if i in after: return 4
        if st.role in ("done", "final"): return 3
        return 2
    def key(i):
        st = steps[i]
        sp = st.story_pos()
        return (group(i), sp if sp is not None else 0, level[i], st.var_rank(), st.script)
    out, seen = [], set()
    for i in sorted(range(n), key=key):
        if i in drop: continue
        st = steps[i]
        st.after_done = group(i) == 4
        if group(i) == 0 and st.role == "step": st.role = "unlock"
        k = (st.role, st.trigger(), tuple(st.merged_conds), tuple(st.action_texts()))
        if k in seen: continue
        seen.add(k); out.append(st)
    return out


# --------------------------------------------------------------- output --
def where_to_find(g, item_id, limit=4):
    name = g.item(item_id)
    rows = [r for r in g.items_csv if r["itemName"] == name]
    good = [r for r in rows if not r["source"].endswith("?")]
    rows = good or rows
    out = []
    for r in rows[:limit]:
        src = {"itemBall": "item ball", "hidden": "hidden item", "gift": "given by an NPC",
               "found": "found", "gift?": "given (unconfirmed)", "found?": "found (unconfirmed)"}.get(r["source"], r["source"])
        at = "%s (%s)%s" % (r["route"], r["mapId"], " %s,%s" % (r["x"], r["y"]) if r["x"] else "")
        out.append("%s: %s" % (src, at))
    if len(rows) > limit: out.append("+%d more" % (len(rows) - limit))
    return out


def where_to_catch(g, sp, limit=3):
    name = g.species(sp)
    rows = [r for r in g.enc_csv if r["pokemonName"] == name]
    rows.sort(key=lambda r: -float(r["encounterRate"] or 0))
    return ["%s, %s %s%%" % (r["route"], r["encounterType"], r["encounterRate"]) for r in rows[:limit]]


def render(an, q, steps, md, rows):
    g = an.g
    o = g.qt + SIDE_QUEST_SIZE * q
    desc = decode(g.rom, g.rom.off(g.rom.u32(o + 4)))
    done = decode(g.rom, g.rom.off(g.rom.u32(o + 8)))
    loc = decode(g.rom, g.rom.off(g.rom.u32(o + 12)))
    md.append('## %d. "%s"\n' % (q + 1, g.qnames[q]))
    md.append("_%s_ — quest menu location: %s\n" % (desc, loc))
    if not steps:
        md.append("_No script starts or completes this quest._\n")
    has_done = any(s.role == "done" for s in steps)
    n, after_hdr = 0, False
    for st in steps:
        if st.after_done and not after_hdr:
            md.append("\n**Afterwards:**\n"); after_hdr = True
        n += 1
        label = {"unlock": "Before starting", "start": "Start", "done": "Complete", "story": "Story", "step": "",
                 "final": "Finish"}[st.role]
        conds = getattr(st, "merged_conds", None)
        if conds is None: conds = st.condition_texts()
        fin = [c for c in conds if c.startswith("after finishing quest ")]
        if len(fin) > 3:
            nums = sorted(int(c.split()[3]) for c in fin)
            conds = [c for c in conds if c not in fin]
            conds.insert(0, "after finishing quests %s (%d quests)" % (", ".join(map(str, nums)), len(nums)))
        head = st.trigger()
        if conds: head += " — " + ", ".join(conds)
        md.append("%d. %s%s" % (n, "**%s:** " % label if label else "", head))
        sub = " " * len("%d. " % n)      # nested bullets must line up with the item text (10. needs 4 spaces)
        acts = st.action_texts()
        for a in acts: md.append(sub + "- " + a)
        for it in st.needed_items():
            w = where_to_find(g, it)
            md.append(sub + "- Where to find %s: %s" % (g.item(it), "; ".join(w) if w else "not in items.csv (shop, berry tree or native code?)"))
        for sp in st.needed_species():
            w = where_to_catch(g, sp)
            md.append(sub + "- Where to catch %s: %s" % (g.species(sp), "; ".join(w) if w else "no wild encounter found"))
        locs = an.where[st.script]
        m, x, y = locs[0][0], locs[0][1], locs[0][2]
        rows.append([q + 1, g.qnames[q], n, st.role + ("/after" if st.after_done else ""),
                     g.mapname(m), "%d.%d" % tuple(m[:2]), x, y, head, " | ".join(acts), "0x%X" % (st.script + ROM_BASE)])
    if not has_done and steps:
        md.append("\n_No script marks this quest as completed in the quest menu._")
    # items the quest scripts check for that no step above explains
    shown = {it for st in steps for it in st.needed_items()}
    extra = []
    for st in an.quest_paths_all(q):
        for cnd in st.conds:
            if cnd[0] == "var" and cnd[4] and cnd[4][0] == "has_item" and Step.positive(cnd) and cnd[4][1] not in shown:
                shown.add(cnd[4][1]); extra.append(cnd[4][1])
    for it in extra:
        w = where_to_find(g, it)
        md.append("\n- Also needed: **%s** — %s" % (g.item(it), "; ".join(w) if w else "not in items.csv"))
    md.append("")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("rom", nargs="?", default=os.path.join(here, "input", "game.gba"))
    ap.add_argument("-o", "--output", default=os.path.join(here, "output", "quest_steps.md"),
                    help="markdown file; a .csv with the same name is written next to it")
    ap.add_argument("--quest", type=int, action="append", help="only this quest (1-based); repeatable")
    ap.add_argument("--bulk", type=int, default=15, help="ignore paths that change more flags/vars than this")
    a = ap.parse_args()
    log = lambda *x: print(*x, file=sys.stderr)
    rom = Rom(a.rom)
    g = Game(rom, here)
    log("quests            : %d" % g.qn)
    log("natives recognised: %s" % {hex(k): v for k, v in g.native_kind.items()})
    an = Analysis(g, bulk=a.bulk)
    log("scripts / paths   : %d / %d" % (len(an.paths), sum(len(v) for v in an.paths.values())))
    log("story variable    : %s" % ("VAR_%04X" % an.story_var if an.story_var is not None else "-"))
    log("trainer names     : %s" % ("found" if an.trainer_name else "not found"))
    md = ["# Quest walkthrough", "",
          "Generated by `extract_quest_steps.py` from the ROM's event scripts. Locations are "
          "`Map name (group.num) x,y`, the tile coordinates Porymap shows. "
          "Quotes are the first and last line of dialogue of that step.", ""]
    rows = []
    wanted = [q - 1 for q in a.quest] if a.quest else range(g.qn)
    for q in wanted:
        steps = an.quest_steps(q)
        render(an, q, steps, md, rows)
        log("quest %2d: %2d steps  %s" % (q + 1, len(steps), g.qnames[q]))
    os.makedirs(os.path.dirname(os.path.abspath(a.output)), exist_ok=True)
    text = re.sub(r"\n{3,}", "\n\n", "\n".join(md)).rstrip("\n") + "\n"
    with open(a.output, "w", encoding="utf-8") as f: f.write(text)
    cp = os.path.splitext(a.output)[0] + ".csv"
    with open(cp, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["questNumber", "questName", "step", "role", "location", "mapId", "x", "y", "what", "details", "script"])
        w.writerows(rows)
    log("wrote %s and %s" % (a.output, cp))


if __name__ == "__main__":
    main()
