#!/usr/bin/env python3
"""
Item-location extractor for pokeemerald / pokeemerald-expansion based ROMs.

Usage:
    python3 extract_items.py [input/game.gba] [-o output/items.csv]

Output CSV columns:
    route, mapId, x, y, source, itemName, quantity, flag, scriptAddress, notes

source:
    itemBall  - visible item ball on the map
    hidden    - hidden item (Itemfinder / A-press on a tile); x,y = that tile.
                quantity = low 7 bits of the expansion hidden-item byte (0 = 1);
                bit 7 is reported as "underfoot" in notes
    gift      - an NPC / sign / trigger script hands the item over (giveitem);
                x,y = the NPC, sign or trigger tile the script hangs off
    found     - a script "finds" an item (finditem) without being an item ball
    gift?     - giveitem found in the ROM but not reached from any map event
                (shared script, or reached via a command the walker can't follow);
                attributed to the closest map script by address, x,y left empty

Coordinates are map-local tile coordinates as stored in the map's event data
(same numbers Porymap shows). mapId is "group.num".
Reuses the ROM / map-name helpers from extract_encounters.py (same folder).
"""
import argparse, csv, os, re, struct, sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from extract_encounters import (Rom, ROM_BASE, find_map_groups,
                                find_region_map_entries, mapsec_names)

BG_HIDDEN_ITEM = 7
STD_OBTAIN_ITEM, STD_FIND_ITEM = 0, 1

# Event-script command sizes (opcode byte included), pokeemerald + expansion 1.x.
# 0 = unknown/variable -> the walker stops on that path.
CMD_LEN = {
    0x00: 1, 0x01: 1, 0x02: 1, 0x03: 1, 0x04: 5, 0x05: 5, 0x06: 6, 0x07: 6, 0x08: 2, 0x09: 2,
    0x0A: 3, 0x0B: 3, 0x0C: 1, 0x0D: 1, 0x0E: 2, 0x0F: 6, 0x10: 3, 0x11: 6, 0x12: 6, 0x13: 6,
    0x14: 3, 0x15: 9, 0x16: 5, 0x17: 5, 0x18: 5, 0x19: 5, 0x1A: 5, 0x1B: 3, 0x1C: 3, 0x1D: 6,
    0x1E: 6, 0x1F: 6, 0x20: 9, 0x21: 5, 0x22: 5, 0x23: 5, 0x24: 5, 0x25: 3, 0x26: 5, 0x27: 1,
    0x28: 3, 0x29: 3, 0x2A: 3, 0x2B: 3, 0x2C: 5, 0x2D: 1, 0x2E: 1, 0x2F: 3, 0x30: 1, 0x31: 3,
    0x32: 1, 0x33: 4, 0x34: 3, 0x35: 1, 0x36: 3, 0x37: 2, 0x38: 2, 0x39: 8, 0x3A: 8, 0x3B: 8,
    0x3C: 3, 0x3D: 8, 0x3E: 8, 0x3F: 8, 0x40: 8, 0x41: 8, 0x42: 5, 0x43: 1, 0x44: 5, 0x45: 5,
    0x46: 5, 0x47: 5, 0x48: 3, 0x49: 5, 0x4A: 5, 0x4B: 3, 0x4C: 3, 0x4D: 3, 0x4E: 3, 0x4F: 7,
    0x50: 9, 0x51: 3, 0x52: 5, 0x53: 3, 0x54: 5, 0x55: 3, 0x56: 5, 0x57: 7, 0x58: 5, 0x59: 5,
    0x5A: 1, 0x5B: 4, 0x5C: 40, 0x5D: 1, 0x5E: 1, 0x5F: 1, 0x60: 3, 0x61: 3, 0x62: 3, 0x63: 7,
    0x64: 3, 0x65: 4, 0x66: 1, 0x67: 5, 0x68: 1, 0x69: 1, 0x6A: 1, 0x6B: 1, 0x6C: 1, 0x6D: 1,
    0x6E: 3, 0x6F: 5, 0x70: 6, 0x71: 6, 0x72: 1, 0x73: 5, 0x74: 5, 0x75: 5, 0x76: 1, 0x77: 2,
    0x78: 5, 0x79: 15, 0x7A: 3, 0x7B: 5, 0x7C: 3, 0x7D: 4, 0x7E: 2, 0x7F: 4, 0x80: 4, 0x81: 4,
    0x82: 4, 0x83: 4, 0x84: 4, 0x85: 6, 0x86: 5, 0x87: 5, 0x88: 5, 0x89: 3, 0x8A: 4, 0x8B: 1,
    0x8C: 1, 0x8D: 1, 0x8E: 1, 0x8F: 3, 0x90: 6, 0x91: 6, 0x92: 6, 0x93: 4, 0x94: 1, 0x95: 4,
    0x96: 3, 0x97: 2, 0x98: 3, 0x99: 3, 0x9A: 2, 0x9B: 5, 0x9C: 3, 0x9D: 4, 0x9E: 3, 0x9F: 3,
    0xA0: 1, 0xA1: 5, 0xA2: 9, 0xA3: 1, 0xA4: 3, 0xA5: 1, 0xA6: 2, 0xA7: 3, 0xA8: 5, 0xA9: 4,
    0xAA: 9, 0xAB: 3, 0xAC: 5, 0xAD: 5, 0xAE: 1, 0xAF: 5, 0xB0: 5, 0xB1: 8, 0xB2: 1, 0xB3: 3,
    0xB4: 3, 0xB5: 3, 0xB6: 6, 0xB7: 1, 0xB8: 5, 0xB9: 5, 0xBA: 5, 0xBB: 6, 0xBC: 6, 0xBD: 5,
    0xBE: 5, 0xBF: 6, 0xC0: 3, 0xC1: 3, 0xC2: 3, 0xC3: 2, 0xC4: 8, 0xC5: 1, 0xC6: 4, 0xC7: 2,
    0xC8: 5, 0xC9: 1, 0xCA: 1, 0xCB: 1, 0xCC: 6, 0xCD: 3, 0xCE: 3, 0xCF: 1, 0xD0: 3, 0xD1: 8,
    0xD2: 4, 0xD3: 3, 0xD4: 1, 0xD5: 3, 0xD6: 1, 0xD7: 8, 0xD8: 1, 0xD9: 1, 0xDA: 1, 0xDB: 5,
    0xDC: 2, 0xDD: 4, 0xDE: 4, 0xDF: 5, 0xE0: 8, 0xE1: 4, 0xE2: 6,
    0xE5: 5, 0xE7: 3,   # expansion additions seen in this ROM (speaker name ptr, 2-byte arg cmd)
}
END_CMDS = {0x02, 0x03, 0x05, 0x08, 0x0C, 0x0D, 0x24}   # end, return, goto, gotostd, ...
BRANCH_PTR_AT = {0x04: 1, 0x05: 1, 0x06: 2, 0x07: 2}      # call, goto, goto_if, call_if
GIVEITEM_RE = re.compile(rb"\x1a\x00\x80(..)\x1a\x01\x80(..)\x09([\x00\x01])", re.S)


# ------------------------------------------------------------------ items --
def find_items(rom):
    """gItemsInfo via GF ROM header (+0x1C8 in expansion). Returns name lookup."""
    base = None
    for hdr in (0x1C8, 0x1C4):
        p = rom.u32(hdr)
        if rom.isptr(p): base = rom.off(p); break_ok = True; break
    if base is None: raise SystemExit("gItemsInfo not found in ROM header")
    found = None
    for stride in range(8, 0x80, 4):
        for noff in range(0, stride, 4):
            ok = True
            for i in range(1, 30):
                q = rom.u32(base + stride * i + noff)
                if not (rom.isptr(q) and rom.is_clean_text(rom.off(q), 3, 20)): ok = False; break
            if ok: found = (stride, noff); break
        if found: break
    if not found:  # inline names (vanilla layout: name[14] first)
        raise SystemExit("Could not work out the item struct layout")
    stride, noff = found
    count = 0
    rhh = rom.d.find(b"RHHEXP")
    if 0 <= rhh < 0x400: count = rom.u16(rhh + 0x14)
    if not (50 < count < 5000):
        count = 1
        while rom.isptr(rom.u32(base + stride * count + noff)): count += 1
    def name(i):
        if i == 0 or i >= count: return "ITEM_%d" % i
        return rom.text(rom.off(rom.u32(base + stride * i + noff)), 30)
    return base, stride, count, name


# ------------------------------------------------------------------- maps --
def iter_maps(rom, mg):
    """Yield (group, num, mapHeaderOffset). Group arrays have no length, so a
    group ends at the next pointer that isn't a map header or at another group."""
    groups = []
    g = 0
    while True:
        p = rom.u32(mg + 4 * g)
        if not rom.isptr(p): break
        groups.append(rom.off(p)); g += 1
    starts = set(groups)
    for gi, gs in enumerate(groups):
        n = 0
        while True:
            o = gs + 4 * n
            if n and o in starts: break
            p = rom.u32(o)
            if not rom.isptr(p): break
            mh = rom.off(p)
            if not all(rom.isptr(rom.u32(mh + k)) for k in (0, 4, 8)): break
            lay = rom.off(rom.u32(mh))
            w, h = struct.unpack_from("<ii", rom.d, lay)
            if not (0 < w <= 1024 and 0 < h <= 1024): break
            yield gi, n, mh
            n += 1


# ----------------------------------------------------------- script walker --
class Walker:
    def __init__(self, rom):
        self.rom = rom

    def walk(self, start, max_nodes=4000):
        """Follow a script and its call/goto branches. Returns
        (gifts, finds, dynamic_find, visited_addresses)."""
        rom, d = self.rom, self.rom.d
        todo, seen = [start], set()
        gifts, finds, dynamic = [], [], False
        visited = set()
        steps = 0
        while todo and steps < max_nodes:
            pc = todo.pop()
            regs = {}
            while 0 <= pc < rom.L and pc not in seen and steps < max_nodes:
                seen.add(pc); steps += 1
                op = d[pc]
                ln = CMD_LEN.get(op, 0)
                if not ln: break
                visited.add(pc)
                if op == 0x1A:   # setorcopyvar var, value
                    regs[rom.u16(pc + 1)] = rom.u16(pc + 3)
                elif op == 0x09 and d[pc + 1] in (STD_OBTAIN_ITEM, STD_FIND_ITEM):
                    item, qty = regs.get(0x8000), regs.get(0x8001, 1)
                    if item is not None:
                        if item >= 0x4000:
                            if d[pc + 1] == STD_FIND_ITEM: dynamic = True
                        else:
                            (gifts if d[pc + 1] == STD_OBTAIN_ITEM else finds).append(
                                (item, qty if qty < 0x4000 else "var", pc))
                elif op == 0x44:  # additem (silent)
                    item, qty = rom.u16(pc + 1), rom.u16(pc + 3)
                    if item < 0x4000: gifts.append((item, qty if qty < 0x4000 else "var", pc))
                if op in BRANCH_PTR_AT:
                    t = rom.u32(pc + BRANCH_PTR_AT[op])
                    if rom.isptr(t): todo.append(rom.off(t))
                elif op == 0x5C:  # expansion trainerbattle: continue/edge scripts inside the params
                    for k in (13, 36):
                        t = rom.u32(pc + k)
                        if rom.isptr(t): todo.append(rom.off(t))
                if op in END_CMDS: break
                pc += ln
        return gifts, finds, dynamic, visited


# ------------------------------------------------------------------- main --
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("rom", nargs="?", default=os.path.join(here, "input", "game.gba"))
    ap.add_argument("-o", "--output", default=os.path.join(here, "output", "items.csv"))
    ap.add_argument("--map-groups", type=lambda s: int(s, 0))
    ap.add_argument("--region-map-entries", type=lambda s: int(s, 0))
    ap.add_argument("--no-orphans", action="store_true", help="drop 'gift?' rows")
    a = ap.parse_args()
    log = lambda *x: print(*x, file=sys.stderr)

    rom = Rom(a.rom)
    ib, istride, icount, item_name = find_items(rom)
    log("gItemsInfo        @ 0x%X  (%d items, %d bytes each)" % (ib, icount, istride))
    mg = a.map_groups if a.map_groups is not None else find_map_groups(rom)[0]
    rme = a.region_map_entries if a.region_map_entries is not None else find_region_map_entries(rom)
    names = mapsec_names(rom, rme) if rme is not None else []
    log("gMapGroups        @ 0x%X" % mg)
    log("gRegionMapEntries @ %s (%d names)" % (hex(rme) if rme is not None else "-", len(names)))

    maps = list(iter_maps(rom, mg))
    log("maps              : %d" % len(maps))

    def route(mh):
        sec = rom.d[mh + 0x14]
        return names[sec] if sec < len(names) and names[sec] else "MAPSEC_%d" % sec

    # --- collect every script entry point together with where it lives
    entries = []   # (scriptOffset, map, x, y, kind, extra)
    balls = []     # (map, x, y, objOffset)
    hidden = []
    script_use = Counter()
    for g, n, mh in maps:
        mid = "%d.%d" % (g, n)
        ev = rom.u32(mh + 4)
        if rom.isptr(ev):
            ev = rom.off(ev)
            oc, wc, cc, bc = rom.d[ev:ev + 4]
            op, cp, bp = rom.u32(ev + 4), rom.u32(ev + 12), rom.u32(ev + 16)
            if rom.isptr(op):
                op = rom.off(op)
                for i in range(oc):
                    o = op + 24 * i
                    x, y = struct.unpack_from("<hh", rom.d, o + 4)
                    s = rom.u32(o + 16)
                    if rom.isptr(s):
                        script_use[rom.off(s)] += 1
                        entries.append((rom.off(s), (g, n, mh), x, y, "object", o))
            if rom.isptr(cp):
                cp = rom.off(cp)
                for i in range(cc):
                    o = cp + 16 * i
                    x, y = struct.unpack_from("<HH", rom.d, o)
                    s = rom.u32(o + 12)
                    if rom.isptr(s): entries.append((rom.off(s), (g, n, mh), x, y, "trigger", o))
            if rom.isptr(bp):
                bp = rom.off(bp)
                for i in range(bc):
                    o = bp + 12 * i
                    x, y = struct.unpack_from("<HH", rom.d, o)
                    kind = rom.d[o + 5]
                    if kind == BG_HIDDEN_ITEM:
                        item = rom.u16(o + 8); hid = rom.d[o + 10]; qb = rom.d[o + 11]
                        hidden.append(((g, n, mh), x, y, item, (qb & 0x7F) or 1, hid, qb >> 7))
                    elif kind <= 4:
                        s = rom.u32(o + 8)
                        if rom.isptr(s): entries.append((rom.off(s), (g, n, mh), x, y, "sign", o))
        # map scripts (on load / on frame / ...): no coordinates
        ms = rom.u32(mh + 8)
        if rom.isptr(ms):
            ms = rom.off(ms)
            for k in range(16):
                t = rom.d[ms + 5 * k]
                if t == 0: break
                p = rom.u32(ms + 5 * k + 1)
                if not rom.isptr(p): break
                p = rom.off(p)
                if t in (2, 4):   # table of (var, value, script)
                    for j in range(32):
                        if rom.u16(p + 8 * j) == 0: break
                        s = rom.u32(p + 8 * j + 4)
                        if rom.isptr(s): entries.append((rom.off(s), (g, n, mh), "", "", "mapscript", None))
                else:
                    entries.append((p, (g, n, mh), "", "", "mapscript", None))

    # --- walk scripts
    W = Walker(rom)
    rows, reached = [], set()
    cache = {}
    for s, (g, n, mh), x, y, kind, o in entries:
        if s not in cache: cache[s] = W.walk(s)
        gifts, finds, dynamic, visited = cache[s]
        reached |= visited
        base = [route(mh), "%d.%d" % (g, n), x, y]
        if kind == "object" and dynamic and rom.u16(o + 14):
            # expansion item ball: item in trainerRange_berryTreeId, amount in movementRangeX
            item = rom.u16(o + 14); qty = (rom.d[o + 10] & 0xF) or 1; flag = rom.u16(o + 20)
            rows.append(base + ["itemBall", item_name(item), qty, "0x%X" % flag, "0x%X" % (s + ROM_BASE)])
            continue
        flag = "0x%X" % rom.u16(o + 20) if kind == "object" else ""
        for item, qty, pc in finds:
            src = "itemBall" if kind == "object" and script_use[s] == 1 else "found"
            rows.append(base + [src, item_name(item), qty, flag, "0x%X" % (pc + ROM_BASE)])
        for item, qty, pc in gifts:
            rows.append(base + ["gift", item_name(item), qty, "", "0x%X" % (pc + ROM_BASE)])

    for (g, n, mh), x, y, item, qty, hid, underfoot in hidden:
        rows.append([route(mh), "%d.%d" % (g, n), x, y, "hidden", item_name(item), qty,
                     "hidden#%d" % hid, "", "underfoot" if underfoot else ""])

    # --- giveitem patterns the walker never reached
    if not a.no_orphans:
        anchors = sorted((s, mid) for s, mid, *_ in entries)
        import bisect
        keys = [k for k, _ in anchors]
        for m in GIVEITEM_RE.finditer(rom.d):
            pc = m.start() + 10
            if pc in reached: continue
            item = struct.unpack("<H", m.group(1))[0]; qty = struct.unpack("<H", m.group(2))[0]
            if item >= 0x4000: continue
            i = bisect.bisect_right(keys, pc) - 1
            if i < 0 or pc - keys[i] > 0x2000: r, mid = "unknown", ""
            else:
                g, n, mh = anchors[i][1]; r, mid = route(mh), "%d.%d" % (g, n)
            src = "gift?" if m.group(3) == b"\x00" else "found?"
            rows.append([r, mid, "", "", src, item_name(item), qty if qty < 0x4000 else "var",
                         "", "0x%X" % (pc + ROM_BASE)])

    uniq, seen_rows = [], set()
    for r in rows:
        k = tuple(r)
        if k not in seen_rows: seen_rows.add(k); uniq.append(r)
    rows = uniq

    os.makedirs(os.path.dirname(os.path.abspath(a.output)), exist_ok=True)
    with open(a.output, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["route", "mapId", "x", "y", "source", "itemName", "quantity", "flag", "scriptAddress", "notes"])
        w.writerows(rows)
    c = Counter(r[4] for r in rows)
    log("wrote %d rows -> %s  %s" % (len(rows), a.output, dict(c)))


if __name__ == "__main__":
    main()
