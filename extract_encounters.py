#!/usr/bin/env python3
"""
Wild-encounter extractor for pokeemerald / pokeemerald-expansion based ROMs.

Usage:
    python3 extract_encounters.py [input/game.gba] [-o output/encounters.csv]

Output CSV columns:
    route, encounterType, day/night, pokemonName, encounterRate, catchRate

Everything is located by signature scanning, so it keeps working when the hack
gets rebuilt and tables move. Every table address can be forced with a flag
(see --help) if auto-detection ever picks the wrong thing.

Notes
- encounterRate = % chance that this species is picked when an encounter of
  this type triggers (duplicate slots of the same species are summed).
- Slot odds are the vanilla/expansion defaults (land 20/20/10/10/10/10/5/5/4/4/1/1,
  water & rock smash 60/30/5/4/1, old rod 70/30, good rod 60/20/20,
  super rod 40/40/15/4/1). Edit SLOT_RATES if a hack changes them.
- Fishing is split into Old/Good/Super Rod.
- day/night: expansion stores one encounter block per time of day. If a map only
  has the default block filled, the row is labelled "any".
- Maps sharing a region-map name get their map id appended, e.g. "Challenger Rd. (1.85)".
  Maps with several encounter sets (Altering-Cave style) get " [set N]".
"""
import argparse, csv, os, struct, sys
from collections import OrderedDict

ROM_BASE = 0x08000000

# ---------------------------------------------------------------- slot odds --
SLOT_RATES = {
    "land":      [20, 20, 10, 10, 10, 10, 5, 5, 4, 4, 1, 1],
    "water":     [60, 30, 5, 4, 1],
    "rockSmash": [60, 30, 5, 4, 1],
    "fishing":   [70, 30, 60, 20, 20, 40, 40, 15, 4, 1],
    "hidden":    [34, 33, 33],   # expansion hidden mons; unused by most hacks
}
FISHING_RODS = [("oldRod", 0, 2), ("goodRod", 2, 5), ("superRod", 5, 10)]
TYPE_ORDER = ["land", "water", "rockSmash", "fishing", "hidden", "extra"]
TOD_LABELS = ["morning", "day", "evening", "night"]

# ------------------------------------------------------------------ charmap --
CHARMAP = {0x00: " ", 0x1B: "é", 0x2D: "&", 0x53: "PK", 0x54: "MN", 0x5A: "Í",
           0xAB: "!", 0xAC: "?", 0xAD: ".", 0xAE: "-", 0xB0: "…", 0xB1: '"',
           0xB2: '"', 0xB3: "'", 0xB4: "'", 0xB5: "♂", 0xB6: "♀", 0xB8: ",",
           0xBA: "/", 0xF0: ":", 0xFE: " "}
for i in range(10): CHARMAP[0xA1 + i] = chr(48 + i)
for i in range(26):
    CHARMAP[0xBB + i] = chr(65 + i)
    CHARMAP[0xD5 + i] = chr(97 + i)


class Rom:
    def __init__(self, path):
        with open(path, "rb") as f:
            self.d = f.read()
        self.L = len(self.d)

    def u8(self, o): return self.d[o]
    def u16(self, o): return struct.unpack_from("<H", self.d, o)[0]
    def u32(self, o): return struct.unpack_from("<I", self.d, o)[0]
    def isptr(self, p): return ROM_BASE <= p < ROM_BASE + self.L
    def off(self, p): return p - ROM_BASE

    def text(self, o, maxlen=40):
        out, d, i = [], self.d, o
        while i < o + maxlen and i < self.L:
            c = d[i]
            if c == 0xFF: break
            if c in (0xFC, 0xFD): i += 2; continue
            out.append(CHARMAP.get(c, ""))
            i += 1
        return "".join(out).strip()

    def is_clean_text(self, o, minlen=2, maxlen=20):
        seg = self.d[o:o + maxlen + 1]
        if 0xFF not in seg: return False
        seg = seg[:seg.index(0xFF)]
        return len(seg) >= minlen and all(c in CHARMAP for c in seg)


# ----------------------------------------------------------------- species --
def find_species(rom, forced_base=None):
    """Returns (base, stride, nameOffset, catchRateOffset, count)."""
    d = rom.d
    count = None
    rhh = d.find(b"RHHEXP")
    if 0 <= rhh < 0x400:
        count = rom.u16(rhh + 12)
    if forced_base is not None:
        base = forced_base
    else:
        base = rom.off(rom.u32(0x1BC))  # GF ROM header -> gSpeciesInfo (expansion)
    # name of SPECIES_NONE is "??????????"
    qm = bytes([0xAC] * 10 + [0xFF])
    noff = d.find(qm, base, base + 0x200)
    if noff < 0:
        raise SystemExit("Could not find species names in gSpeciesInfo at 0x%X "
                         "(vanilla-layout ROMs need --species-info)" % base)
    noff -= base
    for stride in range(0x1C, 0x400, 4):
        if all(rom.is_clean_text(base + stride * i + noff, 3, 12) for i in range(1, 40)):
            break
    else:
        raise SystemExit("Could not determine SpeciesInfo struct size")
    if count is None:
        count = 1
        while rom.is_clean_text(base + stride * count + noff, 2, 12): count += 1
    return base, stride, noff, 8, count


# ------------------------------------------------------------- map metadata --
def find_map_groups(rom):
    d, L = rom.d, rom.L
    def is_mh(p):
        if not rom.isptr(p) or p & 3: return False
        o = rom.off(p)
        if o + 0x1C > L: return False
        a, b, c, e = struct.unpack_from("<4I", d, o)
        return rom.isptr(a) and rom.isptr(b) and rom.isptr(c) and (e == 0 or rom.isptr(e))
    def is_group(p):
        if not rom.isptr(p) or p & 3: return False
        o = rom.off(p)
        return o + 4 <= L and is_mh(rom.u32(o))
    for o in range(0, L - 64, 4):
        p = rom.u32(o)
        if not (ROM_BASE <= p < ROM_BASE + L): continue
        n = 0
        while is_group(rom.u32(o + 4 * n)): n += 1
        if n >= 10: return o, n
    return None, 0


def find_region_map_entries(rom):
    d = rom.d
    def ok(o):
        x, y, w, h = d[o:o + 4]
        p = rom.u32(o + 4)
        if not rom.isptr(p) or not (0 < w <= 40 and 0 < h <= 40 and x <= 60 and y <= 40):
            return False
        return rom.is_clean_text(rom.off(p), 3, 24)
    for o in range(0, rom.L - 8, 4):
        if not rom.isptr(rom.u32(o + 4)): continue
        n = 0
        while ok(o + 8 * n): n += 1
        if n >= 40: return o
    return None


def mapsec_names(rom, entries):
    names, k = [], 0
    while True:
        p = rom.u32(entries + 8 * k + 4)
        if not rom.isptr(p): break
        names.append(rom.text(rom.off(p)))
        k += 1
    return names


# ---------------------------------------------------------- wild headers --
def info_ok(rom, p):
    if not rom.isptr(p) or p & 3: return False
    o = rom.off(p)
    if o + 8 > rom.L or rom.d[o + 1:o + 4] != b"\0\0\0": return False
    mp = rom.u32(o + 4)
    if not rom.isptr(mp): return False
    mo = rom.off(mp)
    lo, hi = rom.d[mo], rom.d[mo + 1]
    return 1 <= lo <= 100 and 1 <= hi <= 100


def find_wild_headers(rom):
    """Find all header tables (main + frontier ones); return (start, stride, count) of the
    table with the most encounter data."""
    d = rom.d
    cands = [o for o in range(0, rom.L - 4, 4)
             if ROM_BASE <= rom.u32(o) < ROM_BASE + rom.L and info_ok(rom, rom.u32(o))]
    best = None
    tried = set()
    for c in cands:
        for stride in range(20, 4 + 4 * 40 + 1, 4):
            for slot in range((stride - 4) // 4):
                h = c - 4 - 4 * slot
                if (h, stride) in tried: continue
                res = walk_table(rom, h, stride)
                if res is None: continue
                start, n, filled = res
                tried.add((start, stride))
                # most data wins; on ties prefer the larger stride (a smaller stride
                # that divides the real one also walks the table, but mis-aligned)
                if best is None or (filled, stride) > (best[3], best[1]):
                    best = (start, stride, n, filled)
        if best and best[3] > 20:
            # good enough once we have a big table; verify a couple more strides only
            break
    if not best:
        raise SystemExit("No wild encounter header table found")
    return best[:3]


def walk_table(rom, h, stride):
    d, np_ = rom.d, (stride - 4) // 4
    def valid(o):
        if o < 0 or o + stride > rom.L or d[o + 2:o + 4] != b"\0\0": return False
        ps = struct.unpack_from("<%dI" % np_, d, o + 4)
        return all(p == 0 or info_ok(rom, p) for p in ps)
    def is_end(o): return d[o] == 0xFF and d[o + 1] == 0xFF
    if not valid(h): return None
    start = h
    while valid(start - stride) and not is_end(start - stride): start -= stride
    o, n, filled = start, 0, 0
    while not is_end(o):
        if not valid(o): return None
        filled += sum(1 for p in struct.unpack_from("<%dI" % np_, d, o + 4) if p)
        n += 1; o += stride
    return start, n, filled


# ------------------------------------------------------------------- main --
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("rom", nargs="?", default=os.path.join(here, "input", "game.gba"))
    ap.add_argument("-o", "--output", default=os.path.join(here, "output", "encounters.csv"))
    ap.add_argument("--wild-headers", type=lambda s: int(s, 0), help="ROM offset of gWildMonHeaders")
    ap.add_argument("--header-size", type=lambda s: int(s, 0), help="sizeof(WildPokemonHeader)")
    ap.add_argument("--species-info", type=lambda s: int(s, 0), help="ROM offset of gSpeciesInfo")
    ap.add_argument("--map-groups", type=lambda s: int(s, 0), help="ROM offset of gMapGroups")
    ap.add_argument("--region-map-entries", type=lambda s: int(s, 0), help="ROM offset of gRegionMapEntries")
    ap.add_argument("--types-per-time", type=int, help="pointer slots per time-of-day block")
    ap.add_argument("--per-slot", action="store_true", help="one row per slot instead of summing per species")
    a = ap.parse_args()

    rom = Rom(a.rom)
    log = lambda *x: print(*x, file=sys.stderr)

    sp_base, sp_stride, sp_name, sp_catch, sp_count = find_species(rom, a.species_info)
    log("gSpeciesInfo      @ 0x%X  (%d species, %d bytes each)" % (sp_base, sp_count, sp_stride))
    def species(s):
        if s >= sp_count: return ("SPECIES_%d" % s, "")
        o = sp_base + s * sp_stride
        return rom.text(o + sp_name, 13), rom.d[o + sp_catch]

    if a.wild_headers is not None:
        hs = a.header_size or 20
        _, n, _ = walk_table(rom, a.wild_headers, hs) or (0, 0, 0)
        wh, hcount = a.wild_headers, n
    else:
        wh, hs, hcount = find_wild_headers(rom)
    np_ = (hs - 4) // 4
    log("gWildMonHeaders   @ 0x%X  (%d headers, %d bytes each, %d pointer slots)" % (wh, hcount, hs, np_))

    per = a.types_per_time or (np_ // 4 if np_ >= 16 and np_ % 4 == 0 else np_)
    n_tod = max(1, np_ // per)

    mg = a.map_groups
    if mg is None: mg, _ = find_map_groups(rom)
    rme = a.region_map_entries if a.region_map_entries is not None else find_region_map_entries(rom)
    names = mapsec_names(rom, rme) if rme is not None else []
    log("gMapGroups        @ %s" % (hex(mg) if mg is not None else "not found"))
    log("gRegionMapEntries @ %s  (%d names)" % (hex(rme) if rme is not None else "not found", len(names)))

    def map_name(g, n):
        if mg is None: return "MAP_%d_%d" % (g, n)
        try:
            gp = rom.off(rom.u32(mg + 4 * g))
            mh = rom.off(rom.u32(gp + 4 * n))
            sec = rom.d[mh + 0x14]
            return names[sec] if sec < len(names) and names[sec] else "MAPSEC_%d" % sec
        except Exception:
            return "MAP_%d_%d" % (g, n)

    # gather headers
    headers = []
    for i in range(hcount):
        o = wh + i * hs
        ps = struct.unpack_from("<%dI" % np_, rom.d, o + 4)
        if any(ps): headers.append((rom.d[o], rom.d[o + 1], ps))

    # route labels: disambiguate shared mapsec names and repeated maps
    base_name = {(g, n): map_name(g, n) for g, n, _ in headers}
    maps_per_name = {}
    for k, v in base_name.items(): maps_per_name.setdefault(v, set()).add(k)
    occurrences = {}
    for g, n, _ in headers: occurrences[(g, n)] = occurrences.get((g, n), 0) + 1
    seen = {}

    rows = []
    for g, n, ps in headers:
        label = base_name[(g, n)]
        if len(maps_per_name[label]) > 1: label += " (%d.%d)" % (g, n)
        if occurrences[(g, n)] > 1:
            seen[(g, n)] = seen.get((g, n), 0) + 1
            label += " [set %d]" % seen[(g, n)]
        used_tods = {t for t in range(n_tod) if any(ps[t * per:(t + 1) * per])}
        for t in range(n_tod):
            if t not in used_tods: continue
            tod = "any" if used_tods == {0} else (TOD_LABELS[t] if t < len(TOD_LABELS) else "tod%d" % t)
            for k in range(per):
                p = ps[t * per + k]
                if not p: continue
                etype = TYPE_ORDER[k] if k < len(TYPE_ORDER) else "type%d" % k
                rates = SLOT_RATES.get(etype)
                if rates is None:
                    log("warning: unknown encounter slot %d on %s, skipped" % (k, label)); continue
                mons_ptr = rom.off(rom.u32(rom.off(p) + 4))
                slots = [struct.unpack_from("<BBH", rom.d, mons_ptr + 4 * s) for s in range(len(rates))]
                groups = [(etype, 0, len(rates))] if etype != "fishing" else FISHING_RODS
                for gname, a0, a1 in groups:
                    agg = OrderedDict()
                    for s in range(a0, a1):
                        lo, hi, spc = slots[s]
                        r = rates[s]
                        key = (spc, s) if a.per_slot else spc
                        agg[key] = agg.get(key, 0) + r
                    total = sum(rates[a0:a1])
                    for key, r in agg.items():
                        spc = key[0] if a.per_slot else key
                        nm, cr = species(spc)
                        pct = round(100.0 * r / total, 2)
                        rows.append([label, gname, tod, nm, ("%g" % pct), cr])

    os.makedirs(os.path.dirname(os.path.abspath(a.output)), exist_ok=True)
    with open(a.output, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["route", "encounterType", "day/night", "pokemonName", "encounterRate", "catchRate"])
        w.writerows(rows)
    log("wrote %d rows -> %s" % (len(rows), a.output))


if __name__ == "__main__":
    main()
