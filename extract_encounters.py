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
import argparse, csv, os, string, struct, sys
from collections import OrderedDict

ROM_BASE = 0x08000000          # GBA address the cartridge ROM is mapped at
ROM_MIRROR_BASE = 0x0A000000   # the same ROM again (wait state 1); some code pointers use this mirror

# GF ROM header / pokeemerald-expansion "RHHEXP" header
ROM_HEADER_SPECIES_INFO = 0x1BC   # GF ROM header field holding the gSpeciesInfo pointer (expansion)
RHH_HEADER_SEARCH_END = 0x400     # the "RHHEXP" magic sits within the first 0x400 bytes of the ROM
RHH_SPECIES_COUNT_OFFSET = 12     # u16 species count, relative to the "RHHEXP" magic

# Sizes of the GBA's basic types
U8_SIZE, U16_SIZE, U32_SIZE = 1, 2, 4
POINTER_SIZE = U32_SIZE
POINTER_ALIGNMENT_MASK = POINTER_SIZE - 1    # pointers to data are 4-byte aligned
SCAN_END_MARGIN = 64                         # table scans stop this many bytes before the end of the ROM

# struct MapHeader
MAP_HEADER_SIZE = 0x1C
MAP_HEADER_LAYOUT, MAP_HEADER_EVENTS, MAP_HEADER_SCRIPTS = 0x00, 0x04, 0x08   # pointer fields
MAP_HEADER_REGION_MAP_SECTION = 0x14         # offset of regionMapSectionId (MAPSEC_*)
MIN_MAP_GROUPS = 10                          # gMapGroups must have at least this many groups

# struct RegionMapLocation { u8 x, y, width, height; const u8 *name; }
REGION_MAP_ENTRY_SIZE = 8
REGION_MAP_ENTRY_NAME = 4                    # offset of the name pointer
REGION_MAP_MAX_X, REGION_MAP_MAX_Y = 60, 40  # plausibility bounds for a region map rectangle
REGION_MAP_MAX_WIDTH, REGION_MAP_MAX_HEIGHT = 40, 40
MAPSEC_NAME_MIN_LENGTH, MAPSEC_NAME_MAX_LENGTH = 3, 24
MIN_REGION_MAP_ENTRIES = 40                  # gRegionMapEntries must have at least this many entries

# struct WildPokemonHeader { u8 mapGroup, mapNum; 2 bytes padding; const struct WildPokemonInfo *infos[]; }
WILD_HEADER_MAP_NUM = 1
WILD_HEADER_PADDING = 2
WILD_HEADER_INFOS = 4                        # offset of the first WildPokemonInfo pointer
MIN_WILD_HEADER_SIZE = 20                    # vanilla: land, water, rock smash and fishing pointers
MAX_WILD_INFO_SLOTS = 40                     # largest number of pointer slots tried per header
ENOUGH_FILLED_SLOTS = 20                     # a header table with more filled slots than this is the main one
MAP_TABLE_END = 0xFF                         # gWildMonHeaders ends with mapGroup = mapNum = 0xFF (MAP_UNDEFINED)
# struct WildPokemonInfo { u8 encounterRate; 3 bytes padding; const struct WildPokemon *wildPokemon; }
WILD_INFO_SIZE = 8
WILD_INFO_PADDING = 1
WILD_INFO_MONS = 4
# struct WildPokemon { u8 minLevel, maxLevel; u16 species; }
WILD_POKEMON_SIZE = 4
WILD_POKEMON_MAX_LEVEL = 1
MAX_LEVEL = 100
MIN_ENCOUNTER_TYPES_PER_TIME = 4             # land, water, rock smash, fishing
ENCOUNTER_RATE_DECIMALS = 2

# gSpeciesInfo layout search
SPECIES_NAME_SEARCH_RANGE = 0x200            # SPECIES_NONE's name must start this close to gSpeciesInfo
MIN_SPECIES_INFO_SIZE, MAX_SPECIES_INFO_SIZE = 0x1C, 0x400
SPECIES_INFO_CATCH_RATE = 8                  # offset of catchRate in struct SpeciesInfo
SPECIES_NONE_NAME_LENGTH = 10                # SPECIES_NONE is called "??????????"
POKEMON_NAME_LENGTH = 12                     # longest species name (pokeemerald-expansion)
SPECIES_LAYOUT_SAMPLE = 40                   # species 1..39 must all have clean names for a struct size to be accepted
LAYOUT_CHECK_MIN_NAME_LENGTH = 3             # names checked while guessing a struct layout are at least this long
MIN_SPECIES_NAME_LENGTH = 2
DEFAULT_TEXT_READ_LENGTH = 40               # Rom.text: bytes read when no length is given
DEFAULT_CLEAN_TEXT_LENGTH = 20              # Rom.is_clean_text: longest string accepted by default

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
TIMES_OF_DAY = len(TOD_LABELS)

# ------------------------------------------------------------------ charmap --
# Control bytes of the game's text encoding (pokeemerald charmap.txt)
CHAR_DIGIT_0, CHAR_UPPER_A, CHAR_LOWER_A = 0xA1, 0xBB, 0xD5   # start of 0-9, A-Z, a-z
CHAR_QUESTION_MARK = 0xAC
CHAR_PROMPT_SCROLL = 0xFA      # \l  scroll the text box up one line
CHAR_PROMPT_CLEAR = 0xFB       # \p  wait for A, then start a new box
EXT_CTRL_CODE_BEGIN = 0xFC     # followed by a control-code id (colour, pause, sound, ...) and its arguments
PLACEHOLDER_BEGIN = 0xFD       # followed by a placeholder id ({PLAYER}, {STR_VAR_1}, ...)
CHAR_NEWLINE = 0xFE            # \n
TEXT_END = 0xFF                # EOS: end of string
CONTROL_SEQUENCE_LENGTH = 2    # EXT_CTRL_CODE_BEGIN / PLACEHOLDER_BEGIN byte + the id that follows it

CHARMAP = {0x00: " ", 0x1B: "é", 0x2D: "&", 0x53: "PK", 0x54: "MN", 0x5A: "Í",
           0xAB: "!", 0xAC: "?", 0xAD: ".", 0xAE: "-", 0xB0: "…", 0xB1: '"',
           0xB2: '"', 0xB3: "'", 0xB4: "'", 0xB5: "♂", 0xB6: "♀", 0xB8: ",",
           0xBA: "/", 0xF0: ":", 0xFE: " "}
for i, char in enumerate(string.digits): CHARMAP[CHAR_DIGIT_0 + i] = char
for i, char in enumerate(string.ascii_uppercase): CHARMAP[CHAR_UPPER_A + i] = char
for i, char in enumerate(string.ascii_lowercase): CHARMAP[CHAR_LOWER_A + i] = char


class Rom:
    def __init__(self, path):
        with open(path, "rb") as rom_file:
            self.data = rom_file.read()
        self.size = len(self.data)

    def u8(self, offset): return self.data[offset]
    def u16(self, offset): return struct.unpack_from("<H", self.data, offset)[0]
    def u32(self, offset): return struct.unpack_from("<I", self.data, offset)[0]
    def isptr(self, pointer): return ROM_BASE <= pointer < ROM_BASE + self.size
    def off(self, pointer): return pointer - ROM_BASE

    def text(self, offset, maxlen=DEFAULT_TEXT_READ_LENGTH):
        out, data, i = [], self.data, offset
        while i < offset + maxlen and i < self.size:
            char_code = data[i]
            if char_code == TEXT_END: break
            if char_code in (EXT_CTRL_CODE_BEGIN, PLACEHOLDER_BEGIN): i += CONTROL_SEQUENCE_LENGTH; continue
            out.append(CHARMAP.get(char_code, ""))
            i += 1
        return "".join(out).strip()

    def is_clean_text(self, offset, minlen=MIN_SPECIES_NAME_LENGTH, maxlen=DEFAULT_CLEAN_TEXT_LENGTH):
        seg = self.data[offset:offset + maxlen + 1]
        if TEXT_END not in seg: return False
        seg = seg[:seg.index(TEXT_END)]
        return len(seg) >= minlen and all(char_code in CHARMAP for char_code in seg)


# ----------------------------------------------------------------- species --
def find_species(rom, forced_base=None):
    """Returns (base, stride, nameOffset, catchRateOffset, count)."""
    data = rom.data
    count = None
    rhh = data.find(b"RHHEXP")
    if 0 <= rhh < RHH_HEADER_SEARCH_END:
        count = rom.u16(rhh + RHH_SPECIES_COUNT_OFFSET)
    if forced_base is not None:
        base = forced_base
    else:
        base = rom.off(rom.u32(ROM_HEADER_SPECIES_INFO))
    # name of SPECIES_NONE is "??????????"
    none_name_bytes = bytes([CHAR_QUESTION_MARK] * SPECIES_NONE_NAME_LENGTH + [TEXT_END])
    noff = data.find(none_name_bytes, base, base + SPECIES_NAME_SEARCH_RANGE)
    if noff < 0:
        raise SystemExit("Could not find species names in gSpeciesInfo at 0x%X "
                         "(vanilla-layout ROMs need --species-info)" % base)
    noff -= base
    for stride in range(MIN_SPECIES_INFO_SIZE, MAX_SPECIES_INFO_SIZE, POINTER_SIZE):
        if all(rom.is_clean_text(base + stride * i + noff, LAYOUT_CHECK_MIN_NAME_LENGTH, POKEMON_NAME_LENGTH)
               for i in range(1, SPECIES_LAYOUT_SAMPLE)):
            break
    else:
        raise SystemExit("Could not determine SpeciesInfo struct size")
    if count is None:
        count = 1
        while rom.is_clean_text(base + stride * count + noff, MIN_SPECIES_NAME_LENGTH, POKEMON_NAME_LENGTH): count += 1
    return base, stride, noff, SPECIES_INFO_CATCH_RATE, count


# ------------------------------------------------------------- map metadata --
def find_map_groups(rom):
    data, rom_size = rom.data, rom.size
    def is_mh(pointer):
        if not rom.isptr(pointer) or pointer & POINTER_ALIGNMENT_MASK: return False
        offset = rom.off(pointer)
        if offset + MAP_HEADER_SIZE > rom_size: return False
        layout_pointer, events_pointer, scripts_pointer, connections_pointer = struct.unpack_from("<4I", data, offset)
        return (rom.isptr(layout_pointer) and rom.isptr(events_pointer) and rom.isptr(scripts_pointer)
                and (connections_pointer == 0 or rom.isptr(connections_pointer)))
    def is_group(pointer):
        if not rom.isptr(pointer) or pointer & POINTER_ALIGNMENT_MASK: return False
        offset = rom.off(pointer)
        return offset + POINTER_SIZE <= rom_size and is_mh(rom.u32(offset))
    for offset in range(0, rom_size - SCAN_END_MARGIN, POINTER_SIZE):
        pointer = rom.u32(offset)
        if not (ROM_BASE <= pointer < ROM_BASE + rom_size): continue
        group_count = 0
        while is_group(rom.u32(offset + POINTER_SIZE * group_count)): group_count += 1
        if group_count >= MIN_MAP_GROUPS: return offset, group_count
    return None, 0


def find_region_map_entries(rom):
    data = rom.data
    def is_entry(offset):
        x, y, width, height = data[offset:offset + REGION_MAP_ENTRY_NAME]
        name_pointer = rom.u32(offset + REGION_MAP_ENTRY_NAME)
        if not rom.isptr(name_pointer) or not (0 < width <= REGION_MAP_MAX_WIDTH and 0 < height <= REGION_MAP_MAX_HEIGHT
                                               and x <= REGION_MAP_MAX_X and y <= REGION_MAP_MAX_Y):
            return False
        return rom.is_clean_text(rom.off(name_pointer), MAPSEC_NAME_MIN_LENGTH, MAPSEC_NAME_MAX_LENGTH)
    for offset in range(0, rom.size - REGION_MAP_ENTRY_SIZE, POINTER_SIZE):
        if not rom.isptr(rom.u32(offset + REGION_MAP_ENTRY_NAME)): continue
        entry_count = 0
        while is_entry(offset + REGION_MAP_ENTRY_SIZE * entry_count): entry_count += 1
        if entry_count >= MIN_REGION_MAP_ENTRIES: return offset
    return None


def mapsec_names(rom, entries):
    names, k = [], 0
    while True:
        name_pointer = rom.u32(entries + REGION_MAP_ENTRY_SIZE * k + REGION_MAP_ENTRY_NAME)
        if not rom.isptr(name_pointer): break
        names.append(rom.text(rom.off(name_pointer)))
        k += 1
    return names


# ---------------------------------------------------------- wild headers --
def info_ok(rom, pointer):
    if not rom.isptr(pointer) or pointer & POINTER_ALIGNMENT_MASK: return False
    offset = rom.off(pointer)
    if offset + WILD_INFO_SIZE > rom.size or any(rom.data[offset + WILD_INFO_PADDING:offset + WILD_INFO_MONS]): return False
    mons_pointer = rom.u32(offset + WILD_INFO_MONS)
    if not rom.isptr(mons_pointer): return False
    mons_offset = rom.off(mons_pointer)
    min_level, max_level = rom.data[mons_offset], rom.data[mons_offset + WILD_POKEMON_MAX_LEVEL]
    return 1 <= min_level <= MAX_LEVEL and 1 <= max_level <= MAX_LEVEL


def find_wild_headers(rom):
    """Find all header tables (main + frontier ones); return (start, stride, count) of the
    table with the most encounter data."""
    data = rom.data
    cands = [offset for offset in range(0, rom.size - POINTER_SIZE, POINTER_SIZE)
             if ROM_BASE <= rom.u32(offset) < ROM_BASE + rom.size and info_ok(rom, rom.u32(offset))]
    best = None   # (start, stride, header_count)
    best_stride, best_filled = 0, 0
    tried = set()
    max_stride = WILD_HEADER_INFOS + POINTER_SIZE * MAX_WILD_INFO_SLOTS
    for candidate in cands:
        for stride in range(MIN_WILD_HEADER_SIZE, max_stride + 1, POINTER_SIZE):
            for slot in range((stride - WILD_HEADER_INFOS) // POINTER_SIZE):
                header_offset = candidate - WILD_HEADER_INFOS - POINTER_SIZE * slot
                if (header_offset, stride) in tried: continue
                res = walk_table(rom, header_offset, stride)
                if res is None: continue
                start, header_count, filled = res
                tried.add((start, stride))
                # most data wins; on ties prefer the larger stride (a smaller stride
                # that divides the real one also walks the table, but mis-aligned)
                if best is None or (filled, stride) > (best_filled, best_stride):
                    best = (start, stride, header_count)
                    best_stride, best_filled = stride, filled
        if best and best_filled > ENOUGH_FILLED_SLOTS:
            # good enough once we have a big table; verify a couple more strides only
            break
    if not best:
        raise SystemExit("No wild encounter header table found")
    return best


def walk_table(rom, header_offset, stride):
    data, pointer_slots = rom.data, (stride - WILD_HEADER_INFOS) // POINTER_SIZE
    def valid(offset):
        if offset < 0 or offset + stride > rom.size or any(data[offset + WILD_HEADER_PADDING:offset + WILD_HEADER_INFOS]):
            return False
        pointers = struct.unpack_from("<%dI" % pointer_slots, data, offset + WILD_HEADER_INFOS)
        return all(pointer == 0 or info_ok(rom, pointer) for pointer in pointers)
    def is_end(offset): return data[offset] == MAP_TABLE_END and data[offset + WILD_HEADER_MAP_NUM] == MAP_TABLE_END
    if not valid(header_offset): return None
    start = header_offset
    while valid(start - stride) and not is_end(start - stride): start -= stride
    offset, header_count, filled = start, 0, 0
    while not is_end(offset):
        if not valid(offset): return None
        filled += sum(1 for pointer in struct.unpack_from("<%dI" % pointer_slots, data, offset + WILD_HEADER_INFOS) if pointer)
        header_count += 1; offset += stride
    return start, header_count, filled


# ------------------------------------------------------------------- main --
def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    here = os.path.dirname(os.path.abspath(__file__))
    parser.add_argument("rom", nargs="?", default=os.path.join(here, "input", "game.gba"))
    parser.add_argument("-o", "--output", default=os.path.join(here, "output", "encounters.csv"))
    parser.add_argument("--wild-headers", type=lambda text: int(text, 0), help="ROM offset of gWildMonHeaders")
    parser.add_argument("--header-size", type=lambda text: int(text, 0), help="sizeof(WildPokemonHeader)")
    parser.add_argument("--species-info", type=lambda text: int(text, 0), help="ROM offset of gSpeciesInfo")
    parser.add_argument("--map-groups", type=lambda text: int(text, 0), help="ROM offset of gMapGroups")
    parser.add_argument("--region-map-entries", type=lambda text: int(text, 0), help="ROM offset of gRegionMapEntries")
    parser.add_argument("--types-per-time", type=int, help="pointer slots per time-of-day block")
    parser.add_argument("--per-slot", action="store_true", help="one row per slot instead of summing per species")
    args = parser.parse_args()

    rom = Rom(args.rom)
    log = lambda *parts: print(*parts, file=sys.stderr)

    sp_base, sp_stride, sp_name, sp_catch, sp_count = find_species(rom, args.species_info)
    log("gSpeciesInfo      @ 0x%X  (%d species, %d bytes each)" % (sp_base, sp_count, sp_stride))
    def species(species_id):
        if species_id >= sp_count: return ("SPECIES_%d" % species_id, "")
        offset = sp_base + species_id * sp_stride
        return rom.text(offset + sp_name, POKEMON_NAME_LENGTH + 1), rom.data[offset + sp_catch]

    if args.wild_headers is not None:
        header_size = args.header_size or MIN_WILD_HEADER_SIZE
        _, table_length, _ = walk_table(rom, args.wild_headers, header_size) or (0, 0, 0)
        wild_headers, hcount = args.wild_headers, table_length
    else:
        wild_headers, header_size, hcount = find_wild_headers(rom)
    pointer_slots = (header_size - WILD_HEADER_INFOS) // POINTER_SIZE
    log("gWildMonHeaders   @ 0x%X  (%d headers, %d bytes each, %d pointer slots)" % (wild_headers, hcount, header_size, pointer_slots))

    # expansion: one block of encounter-type slots per time of day
    one_block_per_time = pointer_slots >= TIMES_OF_DAY * MIN_ENCOUNTER_TYPES_PER_TIME and pointer_slots % TIMES_OF_DAY == 0
    per = args.types_per_time or (pointer_slots // TIMES_OF_DAY if one_block_per_time else pointer_slots)
    n_tod = max(1, pointer_slots // per)

    map_groups = args.map_groups
    if map_groups is None: map_groups, _ = find_map_groups(rom)
    rme = args.region_map_entries if args.region_map_entries is not None else find_region_map_entries(rom)
    names = mapsec_names(rom, rme) if rme is not None else []
    log("gMapGroups        @ %s" % (hex(map_groups) if map_groups is not None else "not found"))
    log("gRegionMapEntries @ %s  (%d names)" % (hex(rme) if rme is not None else "not found", len(names)))

    def map_name(map_group, map_num):
        if map_groups is None: return "MAP_%d_%d" % (map_group, map_num)
        try:
            group_offset = rom.off(rom.u32(map_groups + POINTER_SIZE * map_group))
            map_header = rom.off(rom.u32(group_offset + POINTER_SIZE * map_num))
            sec = rom.data[map_header + MAP_HEADER_REGION_MAP_SECTION]
            return names[sec] if sec < len(names) and names[sec] else "MAPSEC_%d" % sec
        except Exception:
            return "MAP_%d_%d" % (map_group, map_num)

    # gather headers
    headers = []
    for i in range(hcount):
        header_offset = wild_headers + i * header_size
        info_pointers = struct.unpack_from("<%dI" % pointer_slots, rom.data, header_offset + WILD_HEADER_INFOS)
        if any(info_pointers):
            headers.append((rom.data[header_offset], rom.data[header_offset + WILD_HEADER_MAP_NUM], info_pointers))

    # route labels: disambiguate shared mapsec names and repeated maps
    base_name = {(map_group, map_num): map_name(map_group, map_num) for map_group, map_num, _ in headers}
    maps_per_name = {}
    for map_key, base_label in base_name.items(): maps_per_name.setdefault(base_label, set()).add(map_key)
    occurrences = {}
    for map_group, map_num, _ in headers: occurrences[(map_group, map_num)] = occurrences.get((map_group, map_num), 0) + 1
    seen = {}

    rows = []
    for map_group, map_num, info_pointers in headers:
        label = base_name[(map_group, map_num)]
        if len(maps_per_name[label]) > 1: label += " (%d.%d)" % (map_group, map_num)
        if occurrences[(map_group, map_num)] > 1:
            seen[(map_group, map_num)] = seen.get((map_group, map_num), 0) + 1
            label += " [set %d]" % seen[(map_group, map_num)]
        used_tods = {time_of_day for time_of_day in range(n_tod) if any(info_pointers[time_of_day * per:(time_of_day + 1) * per])}
        for time_of_day in range(n_tod):
            if time_of_day not in used_tods: continue
            tod = "any" if used_tods == {0} else (TOD_LABELS[time_of_day] if time_of_day < len(TOD_LABELS) else "tod%d" % time_of_day)
            for k in range(per):
                info_pointer = info_pointers[time_of_day * per + k]
                if not info_pointer: continue
                etype = TYPE_ORDER[k] if k < len(TYPE_ORDER) else "type%d" % k
                rates = SLOT_RATES.get(etype)
                if rates is None:
                    log("warning: unknown encounter slot %d on %s, skipped" % (k, label)); continue
                mons_ptr = rom.off(rom.u32(rom.off(info_pointer) + WILD_INFO_MONS))
                slots = [struct.unpack_from("<BBH", rom.data, mons_ptr + WILD_POKEMON_SIZE * slot) for slot in range(len(rates))]
                groups = [(etype, 0, len(rates))] if etype != "fishing" else FISHING_RODS
                for gname, first_slot, end_slot in groups:
                    agg = OrderedDict()
                    for slot in range(first_slot, end_slot):
                        min_level, max_level, spc = slots[slot]
                        rate = rates[slot]
                        key = (spc, slot) if args.per_slot else spc
                        agg[key] = agg.get(key, 0) + rate
                    total = sum(rates[first_slot:end_slot])
                    for key, rate in agg.items():
                        spc = key[0] if args.per_slot else key
                        pokemon_name, catch_rate = species(spc)
                        pct = round(100.0 * rate / total, ENCOUNTER_RATE_DECIMALS)
                        rows.append([label, gname, tod, pokemon_name, ("%g" % pct), catch_rate])

    os.makedirs(os.path.dirname(os.path.abspath(args.output)), exist_ok=True)
    with open(args.output, "w", newline="", encoding="utf-8") as csv_file:
        writer = csv.writer(csv_file)
        writer.writerow(["route", "encounterType", "day/night", "pokemonName", "encounterRate", "catchRate"])
        writer.writerows(rows)
    log("wrote %d rows -> %s" % (len(rows), args.output))


if __name__ == "__main__":
    main()
