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
from collections import Counter, OrderedDict, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from extract_encounters import (Rom, ROM_BASE, CHARMAP, find_species, find_map_groups,
                                find_region_map_entries, mapsec_names)
from extract_items import find_items, iter_maps, collect_entries, Walker, learn_native_args

SIDE_QUEST_SIZE = 28
SUB_QUEST_SIZE = 24
SPRITE_TYPES = {1: "object", 2: "item", 3: "pokemon"}

# questmenu <case>, <questId>  (include/constants/quests.h)
QUEST_CASES = {
    0: "openMenu", 1: "unlock", 2: "start", 3: "reward", 4: "complete",
    5: "checkUnlocked", 6: "checkInactive", 7: "checkActive", 8: "checkReward",
    9: "checkComplete", 10: "bufferName",
}
QUESTMENU_OPCODE_DEFAULT = 0xE7
# startquest / completequest macro: closemessage; delay 30; questmenu X, q; questmenu 10, q
MACRO_RE = re.compile(rb"\x68\x28\x1e\x00(.)([\x02\x04])(.)\1\x0a\3", re.S)

# expansion object-event pokemon sprites: OBJ_EVENT_MON | species (+ shiny/female bits)
OBJ_EVENT_MON, OBJ_EVENT_MON_SHINY, OBJ_EVENT_MON_FEMALE = 1 << 14, 1 << 13, 1 << 12

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
FC_ARGS = {0x04: 3, 0x0B: 2, 0x10: 2, 0x07: 0, 0x09: 0, 0x0A: 0, 0x0F: 0, 0x15: 0,
           0x16: 0, 0x17: 0, 0x18: 0}   # default: 1 argument byte


def decode(rom, o, maxlen=600, newline=" "):
    """Full-length game text -> str. Line breaks become `newline`; unknown bytes
    are kept as [XX] so nothing disappears silently."""
    d, out, i = rom.d, [], o
    while i < min(o + maxlen, rom.L):
        c = d[i]
        if c == 0xFF: break
        if c in (0xFE, 0xFA, 0xFB): out.append(newline); i += 1; continue
        if c == 0xFC:
            i += 2 + FC_ARGS.get(d[i + 1], 1); continue
        if c == 0xFD:
            out.append(PLACEHOLDERS.get(d[i + 1], "{VAR_%02X}" % d[i + 1])); i += 2; continue
        ch = CHARMAP.get(c, TEXT_EXTRA.get(c))
        out.append(ch if ch is not None else "[%02X]" % c)
        i += 1
    s = "".join(out)
    return re.sub(r"[ ]{2,}", " ", s).strip() if newline == " " else s.strip()


# ------------------------------------------------------------- quest table --
def text_ptr_ok(rom, v, maxlen=400):
    if not rom.isptr(v): return False
    o = rom.off(v)
    seg = rom.d[o:o + maxlen]
    return 0xFF in seg and seg.index(0xFF) >= 1


def side_quest_ok(rom, o):
    if o + SIDE_QUEST_SIZE > rom.L: return False
    if not all(text_ptr_ok(rom, rom.u32(o + k)) for k in (0, 4, 8, 12)): return False
    if rom.d[o + 18] not in SPRITE_TYPES: return False
    if not rom.is_clean_text(rom.off(rom.u32(o + 12)), 2, 30): return False   # map name
    sq, n = rom.u32(o + 20), rom.d[o + 24]
    if sq == 0: return n == 0
    return rom.isptr(sq) and 0 < n < 100


def find_quest_table(rom):
    """Longest run of SideQuest-shaped entries. Returns (offset, count)."""
    best, o = (None, 0), 0
    while o < rom.L - SIDE_QUEST_SIZE:
        if side_quest_ok(rom, o):
            n, q = 0, o
            while side_quest_ok(rom, q): n += 1; q += SIDE_QUEST_SIZE
            if n > best[1]: best = (o, n)
            o = q
        else:
            o += 4
    return best


# ---------------------------------------------------------------- sprites --
def sprite_label(sprite, stype, species_name, item_name):
    if stype == 2:
        return "item", item_name(sprite)
    if stype == 3:
        return "pokemon", species_name(sprite)
    if sprite & OBJ_EVENT_MON:
        sp = sprite & ~(7 << 12)
        tags = [t for b, t in ((OBJ_EVENT_MON_SHINY, "shiny"), (OBJ_EVENT_MON_FEMALE, "female"))
                if sprite & b]
        return "object (pokemon)", species_name(sp) + (" (%s)" % ", ".join(tags) if tags else "")
    if sprite < len(EXPANSION_GFX_NAMES):
        return "object", EXPANSION_GFX_NAMES[sprite]
    return "object", "hack gfx #%d" % sprite


# ------------------------------------------------------------------- main --
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("rom", nargs="?", default=os.path.join(here, "input", "game.gba"))
    ap.add_argument("-o", "--output", default=os.path.join(here, "output", "quests.csv"),
                    help="quests CSV; quest_events.csv / subquests.csv go next to it")
    ap.add_argument("--quest-table", type=lambda s: int(s, 0), help="force sSideQuests offset")
    ap.add_argument("--quest-count", type=int, help="force the number of quests")
    ap.add_argument("--questmenu-opcode", type=lambda s: int(s, 0),
                    help="script opcode of `questmenu` (auto-detected, 0x%X here)" % QUESTMENU_OPCODE_DEFAULT)
    ap.add_argument("--map-groups", type=lambda s: int(s, 0))
    ap.add_argument("--region-map-entries", type=lambda s: int(s, 0))
    ap.add_argument("--keep-newlines", action="store_true",
                    help="keep the in-game line breaks in descriptions (as \\n)")
    a = ap.parse_args()
    log = lambda *x: print(*x, file=sys.stderr)
    rom = Rom(a.rom)
    nl = "\n" if a.keep_newlines else " "

    # --- lookups
    sb, sstride, snoff, _, scount = find_species(rom)
    species_name = lambda i: (rom.text(sb + sstride * i + snoff, 20) if 0 < i < scount
                              else "SPECIES_%d" % i)
    _, _, _, item_name = find_items(rom)

    # --- quest table
    if a.quest_table is not None:
        qt = a.quest_table
        qn = a.quest_count or 0
        if not qn:
            while side_quest_ok(rom, qt + SIDE_QUEST_SIZE * qn): qn += 1
    else:
        qt, qn = find_quest_table(rom)
        if qt is None: raise SystemExit("No Unbound-style quest table (struct SideQuest) found")
        if a.quest_count: qn = a.quest_count
    log("sSideQuests       @ 0x%X  (%d quests, %d bytes each)" % (qt, qn, SIDE_QUEST_SIZE))

    quests, subrows = [], []
    for i in range(qn):
        o = qt + SIDE_QUEST_SIZE * i
        name, desc, done, mp = (rom.off(rom.u32(o + k)) for k in (0, 4, 8, 12))
        sprite, stype = rom.u16(o + 16), rom.d[o + 18]
        sq, nsub = rom.u32(o + 20), rom.d[o + 24]
        kind, label = sprite_label(sprite, stype, species_name, item_name)
        quests.append(OrderedDict([
            ("questNumber", i + 1), ("questId", i),
            ("name", decode(rom, name)), ("description", decode(rom, desc, newline=nl)),
            ("completedDescription", decode(rom, done, newline=nl)),
            ("location", decode(rom, mp)),
            ("spriteType", kind), ("sprite", label), ("spriteId", sprite),
            ("subquests", nsub),
        ]))
        if sq and nsub:
            for j in range(nsub):
                s = rom.off(sq) + SUB_QUEST_SIZE * j
                skind, slabel = sprite_label(rom.u16(s + 16), rom.d[s + 18], species_name, item_name)
                ptr = lambda k: decode(rom, rom.off(rom.u32(s + k)), newline=nl) if rom.isptr(rom.u32(s + k)) else ""
                subrows.append([i + 1, quests[-1]["name"], j + 1, rom.d[s], ptr(4), ptr(8), ptr(12),
                                skind, slabel, ptr(20)])

    # --- where the quests are used in map scripts
    op = a.questmenu_opcode
    if op is None:
        c = Counter(m.group(1)[0] for m in MACRO_RE.finditer(rom.d))
        op = c.most_common(1)[0][0] if c else QUESTMENU_OPCODE_DEFAULT
    log("questmenu opcode  : 0x%X" % op)

    mg = a.map_groups if a.map_groups is not None else find_map_groups(rom)[0]
    rme = a.region_map_entries if a.region_map_entries is not None else find_region_map_entries(rom)
    names = mapsec_names(rom, rme) if rme is not None else []
    maps = list(iter_maps(rom, mg))
    log("maps              : %d" % len(maps))

    def route(mh):
        sec = rom.d[mh + 0x14]
        return names[sec] if sec < len(names) and names[sec] else "MAPSEC_%d" % sec

    entries, _, _ = collect_entries(rom, maps)
    native_args = learn_native_args(rom, sorted({e[0] for e in entries}))
    W, cache, reached = Walker(rom, native_args), {}, set()
    events = []
    for s, (g, n, mh), x, y, kind, eo in entries:
        if s not in cache:
            visited = cache[s] = W.walk(s)[3]
        visited = cache[s]
        reached |= visited
        for pc in sorted(visited):
            if rom.d[pc] != op: continue
            case, q = rom.d[pc + 1], rom.d[pc + 2]
            if case not in QUEST_CASES or case in (0, 10) or q >= qn: continue   # open menu / buffer name
            events.append([q + 1, quests[q]["name"], QUEST_CASES.get(case, "case%d" % case),
                           route(mh), "%d.%d" % (g, n), x, y, kind, "0x%X" % (pc + ROM_BASE)])

    # startquest/completequest macros the walker never reached (unused/dynamic scripts)
    anchors = sorted((s, m) for s, m, *_ in entries)
    keys = [k for k, _ in anchors]
    for m in MACRO_RE.finditer(rom.d):
        pc = m.start() + 4
        if m.group(1)[0] != op or pc in reached: continue
        q = m.group(3)[0]
        if q >= qn: continue
        k = bisect.bisect_right(keys, pc) - 1
        r, mid = ("unknown", "") if k < 0 or pc - keys[k] > 0x2000 else \
                 (route(anchors[k][1][2]), "%d.%d" % anchors[k][1][:2])
        events.append([q + 1, quests[q]["name"], QUEST_CASES[m.group(2)[0]] + "?", r, mid, "", "",
                       "unreached", "0x%X" % (pc + ROM_BASE)])

    seen, uniq = set(), []
    for e in events:
        if tuple(e) not in seen: seen.add(tuple(e)); uniq.append(e)
    events = sorted(uniq, key=lambda e: (e[0], list(QUEST_CASES.values()).index(e[2].rstrip("?"))
                                         if e[2].rstrip("?") in QUEST_CASES.values() else 99, e[4], e[8]))

    # summarise into the quest rows
    def where(q, actions):
        out = OrderedDict()
        for e in events:
            if e[0] == q and e[2] in actions:
                out["%s (%s)" % (e[3], e[4]) if e[4] else e[3]] = 1
        return "; ".join(out)
    for qr in quests:
        q = qr["questNumber"]
        qr["unlockedAt"] = where(q, {"unlock"})
        qr["startedAt"] = where(q, {"start", "start?"})
        qr["rewardAt"] = where(q, {"reward"})
        qr["completedAt"] = where(q, {"complete", "complete?"})

    # --- write
    out = os.path.abspath(a.output)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f); w.writerow(list(quests[0].keys()))
        for qr in quests: w.writerow(list(qr.values()))
    ev_path = os.path.join(os.path.dirname(out), "quest_events.csv")
    with open(ev_path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["questNumber", "questName", "action", "route", "mapId", "x", "y", "eventKind", "scriptAddress"])
        w.writerows(events)
    log("wrote %d quests -> %s" % (len(quests), out))
    log("wrote %d quest script events -> %s  %s" % (len(events), ev_path, dict(Counter(e[2] for e in events))))
    if subrows:
        sp = os.path.join(os.path.dirname(out), "subquests.csv")
        with open(sp, "w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(["questNumber", "questName", "subquestNumber", "subquestId", "name", "description",
                        "location", "spriteType", "sprite", "label"])
            w.writerows(subrows)
        log("wrote %d subquests -> %s" % (len(subrows), sp))
    else:
        log("no subquests defined")


if __name__ == "__main__":
    main()
