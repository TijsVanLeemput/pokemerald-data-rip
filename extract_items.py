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
from collections import Counter, namedtuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from extract_encounters import (Rom, ROM_BASE, ROM_MIRROR_BASE, RHH_HEADER_SEARCH_END, MAP_HEADER_REGION_MAP_SECTION,
                                MAP_HEADER_LAYOUT, MAP_HEADER_EVENTS, MAP_HEADER_SCRIPTS, U8_SIZE, U16_SIZE, U32_SIZE,
                                POINTER_SIZE, LAYOUT_CHECK_MIN_NAME_LENGTH, MAX_LEVEL,
                                find_map_groups, find_region_map_entries, mapsec_names)

ITEM_COLUMNS = ["route", "mapId", "x", "y", "source", "itemName", "quantity", "flag", "scriptAddress", "notes"]

# A map: its group and number (MAP_GROUP / MAP_NUM) and the ROM offset of its MapHeader
MapRef = namedtuple("MapRef", "group num header")
# One script entry point found in a map's events (x/y are empty for map scripts)
MapEntry = namedtuple("MapEntry", "script map x y kind event_offset")
HiddenItem = namedtuple("HiddenItem", "map x y item quantity hidden_item_id underfoot")
# Result of Walker.walk
WalkResult = namedtuple("WalkResult", "gifts finds dynamic_find visited")

BG_HIDDEN_ITEM = 7
STD_OBTAIN_ITEM, STD_FIND_ITEM = 0, 1
HIDDEN_ITEM_QUANTITY_MASK = 0x7F   # hidden item byte: low 7 bits = quantity, bit 7 = underfoot
HIDDEN_ITEM_UNDERFOOT_BIT = 7
ITEM_BALL_QUANTITY_MASK = 0x0F     # expansion item ball: amount in the low nibble of movementRangeX

ROM_HEADER_ITEMS_INFO = (0x1C8, 0x1C4)   # GF ROM header fields that may hold the gItemsInfo pointer
RHH_ITEMS_COUNT_OFFSET = 0x14            # u16 item count, relative to the "RHHEXP" magic
MIN_ITEM_INFO_SIZE, MAX_ITEM_INFO_SIZE = 8, 0x80   # struct ItemInfo sizes tried
ITEM_NAME_LENGTH = 20
ITEM_LAYOUT_SAMPLE = 30                  # items 1..29 must all have clean names for a struct layout to be accepted
MIN_ITEM_COUNT, MAX_ITEM_COUNT = 50, 5000   # a count read from the RHHEXP header outside this range is ignored

# struct MapEvents { u8 objectEventCount, warpCount, coordEventCount, bgEventCount; then pointers }
MAP_EVENTS_COUNTS = 0
MAP_EVENTS_OBJECTS, MAP_EVENTS_COORDS, MAP_EVENTS_BGS = 4, 12, 16   # (the warps pointer at 8 isn't needed)
# struct ObjectEventTemplate
OBJECT_EVENT_SIZE = 24
OBJECT_EVENT_GRAPHICS_ID = 1         # u16
OBJECT_EVENT_POSITION = 4            # s16 x, s16 y
OBJECT_EVENT_MOVEMENT_RANGE = 10     # movementRangeX/Y; an expansion item ball keeps its amount here
OBJECT_EVENT_TRAINER_RANGE = 14      # trainerRange_berryTreeId; an expansion item ball keeps its item here
OBJECT_EVENT_SCRIPT = 16
OBJECT_EVENT_FLAG = 20               # the object is hidden while this flag is set
# struct CoordEvent (step trigger): u16 x, y; ...; u16 var, value (runs when var == value); script
COORD_EVENT_SIZE = 16
COORD_EVENT_VAR, COORD_EVENT_VALUE = 6, 8
COORD_EVENT_SCRIPT = 12
# struct BgEvent (sign / hidden item): u16 x, y; u8 elevation, kind; ...; script pointer or hidden item data
BG_EVENT_SIZE = 12
BG_EVENT_KIND = 5
BG_EVENT_SCRIPT = 8
BG_EVENT_HIDDEN_ITEM, BG_EVENT_HIDDEN_ITEM_ID, BG_EVENT_HIDDEN_ITEM_QUANTITY = 8, 10, 11
BG_EVENT_LAST_SCRIPT_KIND = 4        # kinds 0-4 are signs that run a script (BG_EVENT_PLAYER_FACING_*)
# Map scripts: list of {u8 type; const u8 *script} (5 bytes, unaligned), ended by type 0
MAP_SCRIPT_ENTRY_SIZE = 5
MAP_SCRIPT_POINTER = 1
MAX_MAP_SCRIPTS = 16
MAP_SCRIPT_ON_FRAME_TABLE, MAP_SCRIPT_ON_WARP_INTO_MAP_TABLE = 2, 4   # these types point to a table, not a script
# ... those tables: {u16 var; u16 value; const u8 *script}, ended by var 0
MAP_SCRIPT_TABLE_ENTRY_SIZE = 8
MAP_SCRIPT_TABLE_VALUE, MAP_SCRIPT_TABLE_SCRIPT = 2, 4
MAX_MAP_SCRIPT_TABLE_ENTRIES = 32
MAX_MAP_DIMENSION = 1024             # sanity bound for a map layout's width / height

# Variables and flags
VARS_START = 0x4000           # script arguments >= this are variable ids, not literal values
VARS_SCAN_END = 0x4200        # var ids above this are not plausible (sanity check while parsing)
SPECIAL_VARS_START, SPECIAL_VARS_END = 0x8000, 0x8020   # VAR_0x8000 ... VAR_RESULT ...
VAR_ITEM_ID, VAR_ITEM_AMOUNT = 0x8000, 0x8001           # callstd giveitem/finditem read VAR_0x8000 / VAR_0x8001
FLAGS_SCAN_END = 0x4100       # special flags start at 0x4000; flag ids from here on are not plausible
MAX_SPECIES_ID = 0x1000       # sanity bound for a species id in createmon arguments
ROM_POINTER_HIGH_BYTES = (0x08, 0x09, 0x0A, 0x0B)       # top byte of a pointer into the ROM or its mirror
MAX_SCRIPT_DISTANCE = 0x2000  # how far apart two scripts of the same map may lie (bytes)
POINTER_HIGH_BYTE_SHIFT = 24
CMD_ARGS = 1                  # a script command's arguments start right after its opcode byte
MIN_COMMANDS_BEFORE_UNKNOWN_NATIVE = 2   # parses_ok: an unknown callnative this far in is accepted
MAX_PARSE_CHECK_COMMANDS = 40   # parses_ok: this many sensible commands in a row count as real script
MAX_WALK_COMMANDS = 4000        # Walker.walk: commands followed per script


class ScriptCmd:
    """Event-script opcodes (pokeemerald data/script_cmd_table.inc). E5-E7 are this ROM's own commands."""
    NOP = 0x00
    NOP1 = 0x01
    END = 0x02
    RETURN = 0x03
    CALL = 0x04
    GOTO = 0x05
    GOTO_IF = 0x06
    CALL_IF = 0x07
    GOTOSTD = 0x08
    CALLSTD = 0x09
    GOTOSTD_IF = 0x0A
    CALLSTD_IF = 0x0B
    RETURNRAM = 0x0C
    ENDRAM = 0x0D
    SETMYSTERYEVENTSTATUS = 0x0E
    LOADWORD = 0x0F
    SETVAR = 0x16
    ADDVAR = 0x17
    SUBVAR = 0x18
    COPYVAR = 0x19
    SETORCOPYVAR = 0x1A
    COMPARE_VAR_TO_VALUE = 0x21
    COMPARE_VAR_TO_VAR = 0x22
    CALLNATIVE = 0x23
    GOTONATIVE = 0x24
    SPECIAL = 0x25
    SPECIALVAR = 0x26
    DELAY = 0x28
    SETFLAG = 0x29
    CLEARFLAG = 0x2A
    CHECKFLAG = 0x2B
    WARP = 0x39
    WARPSILENT = 0x3A
    WARPDOOR = 0x3B
    WARPHOLE = 0x3C
    WARPTELEPORT = 0x3D
    GETPLAYERXY = 0x42
    ADDITEM = 0x44
    REMOVEITEM = 0x45
    CHECKITEM = 0x47
    TRAINERBATTLE = 0x5C
    CHECKTRAINERFLAG = 0x60
    MESSAGE = 0x67
    CLOSEMESSAGE = 0x68
    YESNOBOX = 0x6E
    MULTICHOICE = 0x6F
    MULTICHOICEDEFAULT = 0x70
    MULTICHOICEGRID = 0x71
    GIVEMON = 0x79
    GIVEEGG = 0x7A
    POKEMART = 0x86
    ADDMONEY = 0x90
    REMOVEMONEY = 0x91
    CHECKMONEY = 0x92
    SETWILDBATTLE = 0xB6
    POKENAVCALL = 0xDF
    SETSPEAKERNAME = 0xE5     # this ROM: show a speaker name box (text pointer)
    CLEARSPEAKERNAME = 0xE6   # this ROM: hide it again
    QUESTMENU = 0xE7          # this ROM: questmenu case, questId


# Thumb instructions recognised when measuring how many inline argument bytes a native reads
THUMB_PUSH_R4_R5_LR = 0xB530                                     # optional prologue of the script readers
SCRIPT_READ_BODY = [0x6883, 0x1C5A, 0x6082, 0x1C99, 0x781A, 0x6081]   # shared start of ScriptReadHalfword/Word
THUMB_ADDS_R4_R3_3 = 0x1CDC                                      # only ScriptReadWord continues with this
THUMB_BL_MASK, THUMB_BL_FIRST, THUMB_BL_SECOND = 0xF800, 0xF000, 0xF800   # bl = two halfwords
THUMB_BL_OFFSET_MASK, THUMB_BL_OFFSET_SIGN, THUMB_BL_OFFSET_WRAP = 0x7FF, 0x400, 0x800
THUMB_BX_MASK, THUMB_BX = 0xFF87, 0x4700                         # bx rm (return)
THUMB_POP_PC_MASK, THUMB_POP_PC = 0xFF00, 0xBD00                 # pop {..., pc} (return)
THUMB_LDR_STR_IMM_MASK = 0xFFC0
THUMB_LDR_SCRIPT_PTR, THUMB_STR_SCRIPT_PTR = 0x6880, 0x6080     # ldr/str rd, [rn, #8]  (ScriptContext.scriptPtr)
THUMB_ADDS_IMM3_MASK, THUMB_ADDS_IMM3 = 0xFE00, 0x1C00           # adds rd, rn, #imm3
THUMB_ADDS_IMM8_MASK, THUMB_ADDS_IMM8 = 0xF800, 0x3000           # adds rd, #imm8
THUMB_IMM8_MASK = 0xFF
THUMB_INSTRUCTION_SIZE = 2
THUMB_BL_HALFWORDS = 2                                           # bl is the only two-halfword instruction
THUMB_BL_SIZE = THUMB_BL_HALFWORDS * THUMB_INSTRUCTION_SIZE
THUMB_PC_AHEAD = 4                                               # pc reads 4 bytes past the executing instruction
THUMB_BL_HIGH_SHIFT, THUMB_BL_LOW_SHIFT = 12, 1
THUMB_REGISTER_MASK = 7                                          # 3-bit register fields
THUMB_ADDS_IMM3_SHIFT = 6                                        # adds rd, rn, #imm3: imm3 in bits 6-8
THUMB_ADDS_IMM8_REGISTER_SHIFT = 8                               # adds rd, #imm8: rd in bits 8-10
READER_CHECK_HALFWORDS = 8                                       # instructions compared to recognise ScriptRead*
MAX_NATIVE_INSTRUCTIONS = 600                                    # stop reading a native after this many
MAX_LOOKBACK = 5                                                 # how far back to look for the increment before a str

# Event-script command sizes (opcode byte included), pokeemerald + expansion 1.x. Keys are ScriptCmd opcodes.
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
    0xE5: 5, 0xE6: 1, 0xE7: 3,   # this ROM: E5 = set speaker name (ptr), E6 = clear it (no args), E7 = questmenu case, quest
    0xE8: 6, 0xE9: 2, 0xEA: 1,   # subquestmenu, returnqueststate, + one more (lengths read from their handlers)
}
END_CMDS = {ScriptCmd.END, ScriptCmd.RETURN, ScriptCmd.GOTO, ScriptCmd.GOTOSTD, ScriptCmd.RETURNRAM,
            ScriptCmd.ENDRAM, ScriptCmd.GOTONATIVE}
# offset of the target pointer in a branch command (goto_if / call_if have a u8 condition first)
BRANCH_PTR_AT = {ScriptCmd.CALL: CMD_ARGS, ScriptCmd.GOTO: CMD_ARGS,
                 ScriptCmd.GOTO_IF: CMD_ARGS + U8_SIZE, ScriptCmd.CALL_IF: CMD_ARGS + U8_SIZE}
CALLNATIVE_SIZE = CMD_LEN[ScriptCmd.CALLNATIVE]   # opcode + function pointer; the native's inline arguments follow
# expansion trainerbattle (40 bytes): trainer id and the scripts it can continue with
TRAINERBATTLE_TRAINER = 3
TRAINERBATTLE_CONTINUE_SCRIPT, TRAINERBATTLE_SECOND_SCRIPT = 13, 36
# setorcopyvar VAR_0x8000, item; setorcopyvar VAR_0x8001, amount; callstd STD_OBTAIN_ITEM or STD_FIND_ITEM
GIVEITEM_RE = re.compile(
    re.escape(struct.pack("<BH", ScriptCmd.SETORCOPYVAR, VAR_ITEM_ID)) + b"(?P<item>..)"
    + re.escape(struct.pack("<BH", ScriptCmd.SETORCOPYVAR, VAR_ITEM_AMOUNT)) + b"(?P<amount>..)"
    + re.escape(bytes([ScriptCmd.CALLSTD])) + b"(?P<std>[" + re.escape(bytes([STD_OBTAIN_ITEM, STD_FIND_ITEM])) + b"])",
    re.S)
GIVEITEM_CALLSTD_AT = 2 * CMD_LEN[ScriptCmd.SETORCOPYVAR]   # the callstd follows the two setorcopyvar commands


def command_args(rom, pc, fmt):
    """Unpack the arguments of the script command at pc (struct format, little-endian, unaligned)."""
    return struct.unpack_from("<" + fmt, rom.data, pc + CMD_ARGS)


# ------------------------------------------------------------------ items --
def find_items(rom):
    """gItemsInfo via GF ROM header (ROM_HEADER_ITEMS_INFO). Returns name lookup."""
    base = None
    for hdr in ROM_HEADER_ITEMS_INFO:
        header_pointer = rom.u32(hdr)
        if rom.isptr(header_pointer): base = rom.off(header_pointer); break
    if base is None: raise SystemExit("gItemsInfo not found in ROM header")
    found = None
    for stride in range(MIN_ITEM_INFO_SIZE, MAX_ITEM_INFO_SIZE, POINTER_SIZE):
        for noff in range(0, stride, POINTER_SIZE):
            layout_matches = True
            for i in range(1, ITEM_LAYOUT_SAMPLE):
                name_pointer = rom.u32(base + stride * i + noff)
                if not (rom.isptr(name_pointer)
                        and rom.is_clean_text(rom.off(name_pointer), LAYOUT_CHECK_MIN_NAME_LENGTH, ITEM_NAME_LENGTH)):
                    layout_matches = False; break
            if layout_matches: found = (stride, noff); break
        if found: break
    if not found:  # inline names (vanilla layout: name[14] first)
        raise SystemExit("Could not work out the item struct layout")
    stride, noff = found
    count = 0
    rhh = rom.data.find(b"RHHEXP")
    if 0 <= rhh < RHH_HEADER_SEARCH_END: count = rom.u16(rhh + RHH_ITEMS_COUNT_OFFSET)
    if not (MIN_ITEM_COUNT < count < MAX_ITEM_COUNT):
        count = 1
        while rom.isptr(rom.u32(base + stride * count + noff)): count += 1
    def name(item_id):
        if item_id == 0 or item_id >= count: return "ITEM_%d" % item_id
        return rom.text(rom.off(rom.u32(base + stride * item_id + noff)), ITEM_NAME_LENGTH + 1)
    return base, stride, count, name


# ------------------------------------------------------------------- maps --
def iter_maps(rom, map_groups):
    """Yield a MapRef per map. Group arrays have no length, so a
    group ends at the next pointer that isn't a map header or at another group."""
    groups = []
    group_count = 0
    while True:
        pointer = rom.u32(map_groups + POINTER_SIZE * group_count)
        if not rom.isptr(pointer): break
        groups.append(rom.off(pointer)); group_count += 1
    starts = set(groups)
    for map_group, group_start in enumerate(groups):
        map_num = 0
        while True:
            slot_offset = group_start + POINTER_SIZE * map_num
            if map_num and slot_offset in starts: break
            pointer = rom.u32(slot_offset)
            if not rom.isptr(pointer): break
            map_header = rom.off(pointer)
            if not all(rom.isptr(rom.u32(map_header + field))
                       for field in (MAP_HEADER_LAYOUT, MAP_HEADER_EVENTS, MAP_HEADER_SCRIPTS)): break
            lay = rom.off(rom.u32(map_header + MAP_HEADER_LAYOUT))
            width, height = struct.unpack_from("<ii", rom.data, lay)
            if not (0 < width <= MAX_MAP_DIMENSION and 0 < height <= MAX_MAP_DIMENSION): break
            yield MapRef(map_group, map_num, map_header)
            map_num += 1


# ------------------------------------------------------ callnative args --
# Expansion implements many script commands as `callnative Func` followed by
# inline arguments that Func reads itself (givemon, getobjectxy, checkspecies,
# createfollowernpc, ...). The ROM doesn't say how many bytes each native eats,
# so it's read from the native's Thumb code: calls to ScriptReadHalfword (+2) /
# ScriptReadWord (+4) and inlined byte reads (scriptPtr += n). The guess is then
# checked against the call sites (does the script still parse after it?) and
# nudged by up to +-4 bytes if it doesn't.
MAX_NATIVE_ARGS = 24
NATIVE_ARG_NUDGE = 4
CREATEMON = "createmon"
# createmon / givemon inline arguments: u8 side, u8 slot, u16 species, u16 level, u32 flags, then one u16 per set flag bit
CREATEMON_SIDE, CREATEMON_SLOT, CREATEMON_SPECIES, CREATEMON_LEVEL, CREATEMON_FLAGS = 0, 1, 2, 4, 6
CREATEMON_FIXED_ARGS = 10
CREATEMON_FLAG_BITS = 25
SIDE_PLAYER, SIDE_OPPONENT = 0, 1
PARTY_SIZE = 6


def _rom_off(function_pointer):
    return (function_pointer & ~1) - (ROM_MIRROR_BASE if function_pointer >= ROM_MIRROR_BASE else ROM_BASE)


def _reader_kind(rom, offset):
    """Bytes read by the function at offset: 2 for ScriptReadHalfword, 4 for ScriptReadWord, else 0."""
    halfwords = [rom.u16(offset + THUMB_INSTRUCTION_SIZE * i) for i in range(READER_CHECK_HALFWORDS)]
    if halfwords[0] == THUMB_PUSH_R4_R5_LR: halfwords = halfwords[1:]
    if halfwords[:len(SCRIPT_READ_BODY)] == SCRIPT_READ_BODY:
        return U32_SIZE if halfwords[len(SCRIPT_READ_BODY)] == THUMB_ADDS_R4_R3_3 else U16_SIZE
    return 0


def native_arg_guess(rom, function_pointer, max_instructions=MAX_NATIVE_INSTRUCTIONS):
    offset = _rom_off(function_pointer)
    if not (0 <= offset < rom.size - THUMB_BL_SIZE): return 0
    total, grp, i = 0, None, 0
    while i < max_instructions and offset + THUMB_INSTRUCTION_SIZE * i + THUMB_BL_SIZE < rom.size:
        address = offset + THUMB_INSTRUCTION_SIZE * i
        halfword = rom.u16(address)
        second_halfword = rom.u16(address + THUMB_INSTRUCTION_SIZE)
        if (halfword & THUMB_BL_MASK) == THUMB_BL_FIRST and (second_halfword & THUMB_BL_MASK) == THUMB_BL_SECOND:
            offset_high, offset_low = halfword & THUMB_BL_OFFSET_MASK, second_halfword & THUMB_BL_OFFSET_MASK
            if offset_high & THUMB_BL_OFFSET_SIGN: offset_high -= THUMB_BL_OFFSET_WRAP
            target = address + THUMB_PC_AHEAD + (offset_high << THUMB_BL_HIGH_SHIFT) + (offset_low << THUMB_BL_LOW_SHIFT)
            if 0 <= target < rom.size - READER_CHECK_HALFWORDS * THUMB_INSTRUCTION_SIZE: total += _reader_kind(rom, target)
            i += THUMB_BL_HALFWORDS; continue
        if (halfword & THUMB_BX_MASK) == THUMB_BX or (halfword & THUMB_POP_PC_MASK) == THUMB_POP_PC: break
        if (halfword & THUMB_LDR_STR_IMM_MASK) == THUMB_LDR_SCRIPT_PTR:
            total += grp or 0; grp = 0
        if (halfword & THUMB_LDR_STR_IMM_MASK) == THUMB_STR_SCRIPT_PTR and grp is not None:
            dest_register = halfword & THUMB_REGISTER_MASK
            for k in range(1, MAX_LOOKBACK + 1):
                earlier_halfword = rom.u16(offset + THUMB_INSTRUCTION_SIZE * (i - k))
                if (earlier_halfword & THUMB_ADDS_IMM3_MASK) == THUMB_ADDS_IMM3 \
                        and (earlier_halfword & THUMB_REGISTER_MASK) == dest_register:
                    grp = max(grp, (earlier_halfword >> THUMB_ADDS_IMM3_SHIFT) & THUMB_REGISTER_MASK); break
                if (earlier_halfword & THUMB_ADDS_IMM8_MASK) == THUMB_ADDS_IMM8 \
                        and ((earlier_halfword >> THUMB_ADDS_IMM8_REGISTER_SHIFT) & THUMB_REGISTER_MASK) == dest_register:
                    grp = max(grp, earlier_halfword & THUMB_IMM8_MASK); break
        i += 1
    return total + (grp or 0)


def createmon_args_ok(rom, offset):
    side, slot, species, level, flags = struct.unpack_from("<BBHHI", rom.data, offset + CREATEMON_SIDE)
    return side <= SIDE_OPPONENT and slot <= PARTY_SIZE and 0 < species < MAX_SPECIES_ID and 0 < level <= MAX_LEVEL \
        and flags < (1 << CREATEMON_FLAG_BITS)


def createmon_args_length(rom, pc):
    """Inline argument bytes of a createmon/givemon callnative at pc."""
    flags = rom.u32(pc + CALLNATIVE_SIZE + CREATEMON_FLAGS)
    return CREATEMON_FIXED_ARGS + U16_SIZE * bin(flags).count("1")


def native_len(rom, pc, native_args):
    """Inline argument bytes after `callnative <ptr>` at pc."""
    function_pointer, = command_args(rom, pc, "I")
    arg_bytes = native_args.get(function_pointer, 0)
    if arg_bytes == CREATEMON:
        return createmon_args_length(rom, pc)
    return arg_bytes


def cmd_len(rom, pc, native_args):
    opcode = rom.data[pc]
    length = CMD_LEN.get(opcode, 0)
    if opcode == ScriptCmd.CALLNATIVE and length: length += native_len(rom, pc, native_args)
    return length


def parses_ok(rom, pc, native_args, max_cmds=MAX_PARSE_CHECK_COMMANDS):
    """Does the byte stream at pc look like real script commands up to an end?"""
    data = rom.data
    for command_index in range(max_cmds):
        if not (0 <= pc < rom.size): return False
        opcode = data[pc]
        length = cmd_len(rom, pc, native_args)
        if not length or opcode in (ScriptCmd.NOP, ScriptCmd.NOP1, ScriptCmd.GOTOSTD_IF, ScriptCmd.CALLSTD_IF,
                                      ScriptCmd.SETMYSTERYEVENTSTATUS): return False
        if opcode in BRANCH_PTR_AT and not rom.isptr(rom.u32(pc + BRANCH_PTR_AT[opcode])): return False
        if opcode == ScriptCmd.LOADWORD:
            slot, value = command_args(rom, pc, "BI")
            if not rom.isptr(value): return False
        if opcode in (ScriptCmd.CALLNATIVE, ScriptCmd.GOTONATIVE):
            function_pointer, = command_args(rom, pc, "I")
            if function_pointer >> POINTER_HIGH_BYTE_SHIFT not in ROM_POINTER_HIGH_BYTES: return False
        if opcode in (ScriptCmd.SETVAR, ScriptCmd.ADDVAR, ScriptCmd.SUBVAR, ScriptCmd.COMPARE_VAR_TO_VALUE):
            var_id, = command_args(rom, pc, "H")
            if not (VARS_START <= var_id < VARS_SCAN_END or SPECIAL_VARS_START <= var_id < SPECIAL_VARS_END): return False
        if opcode in (ScriptCmd.SETFLAG, ScriptCmd.CLEARFLAG, ScriptCmd.CHECKFLAG):
            flag_id, = command_args(rom, pc, "H")
            if flag_id >= FLAGS_SCAN_END: return False
        if opcode == ScriptCmd.CALLNATIVE and command_index >= MIN_COMMANDS_BEFORE_UNKNOWN_NATIVE:
            function_pointer, = command_args(rom, pc, "I")
            if function_pointer not in native_args: return True
        if opcode in END_CMDS: return True
        pc += length
    return True   # max_cmds sensible commands in a row


def learn_native_args(rom, starts, rounds=NATIVE_ARG_NUDGE):
    """starts: script offsets. Returns {native target pointer: inline arg bytes (or CREATEMON)}."""
    native_args = {}
    for _ in range(rounds):
        sites = {}
        walker = Walker(rom, native_args)
        for start in starts:
            for pc in walker.walk(start).visited:
                if rom.data[pc] != ScriptCmd.CALLNATIVE: continue
                function_pointer, = command_args(rom, pc, "I")
                sites.setdefault(function_pointer, set()).add(pc)
        new = {}
        for target, pcs in sites.items():
            if target in native_args: continue
            if all(createmon_args_ok(rom, pc + CALLNATIVE_SIZE) for pc in pcs) and \
               sum(parses_ok(rom, pc + CALLNATIVE_SIZE + createmon_args_length(rom, pc), native_args)
                   for pc in pcs) >= len(pcs) / 2:
                new[target] = CREATEMON; continue
            guess = native_arg_guess(rom, target)
            cands = sorted({max(0, min(MAX_NATIVE_ARGS, guess + nudge)) for nudge in range(-NATIVE_ARG_NUDGE, NATIVE_ARG_NUDGE + 1)},
                           key=lambda arg_length: abs(arg_length - guess))
            score = lambda arg_length: sum(parses_ok(rom, pc + CALLNATIVE_SIZE + arg_length, native_args) for pc in pcs)
            best = max(cands, key=lambda arg_length: (score(arg_length), -abs(arg_length - guess)))
            guess_score = score(guess)   # trust the code-derived guess unless most call sites disagree
            new[target] = best if guess_score < len(pcs) / 2 and score(best) > guess_score else guess
        if not new: break
        native_args.update(new)
    return native_args


# ----------------------------------------------------------- script walker --
class Walker:
    def __init__(self, rom, native_args=None):
        self.rom = rom
        self.native_args = native_args or {}

    def walk(self, start, max_nodes=MAX_WALK_COMMANDS):
        """Follow a script and its call/goto branches. Returns a WalkResult."""
        rom, data = self.rom, self.rom.data
        todo, seen = [start], set()
        gifts, finds, dynamic = [], [], False
        visited = set()
        steps = 0
        while todo and steps < max_nodes:
            pc = todo.pop()
            regs = {}
            while 0 <= pc < rom.size and pc not in seen and steps < max_nodes:
                seen.add(pc); steps += 1
                opcode = data[pc]
                length = cmd_len(rom, pc, self.native_args)
                if not length: break
                visited.add(pc)
                if opcode == ScriptCmd.SETORCOPYVAR:
                    var_id, value = command_args(rom, pc, "HH")
                    regs[var_id] = value
                elif opcode == ScriptCmd.CALLSTD:
                    std, = command_args(rom, pc, "B")
                    item, qty = regs.get(VAR_ITEM_ID), regs.get(VAR_ITEM_AMOUNT, 1)
                    if std in (STD_OBTAIN_ITEM, STD_FIND_ITEM) and item is not None:
                        if item >= VARS_START:
                            if std == STD_FIND_ITEM: dynamic = True
                        else:
                            (gifts if std == STD_OBTAIN_ITEM else finds).append(
                                (item, qty if qty < VARS_START else "var", pc))
                elif opcode == ScriptCmd.ADDITEM:  # silent
                    item, qty = command_args(rom, pc, "HH")
                    if item < VARS_START: gifts.append((item, qty if qty < VARS_START else "var", pc))
                if opcode in BRANCH_PTR_AT:
                    target = rom.u32(pc + BRANCH_PTR_AT[opcode])
                    if rom.isptr(target): todo.append(rom.off(target))
                elif opcode == ScriptCmd.TRAINERBATTLE:  # expansion: follow-up scripts inside the params
                    for field in (TRAINERBATTLE_CONTINUE_SCRIPT, TRAINERBATTLE_SECOND_SCRIPT):
                        target = rom.u32(pc + field)
                        if rom.isptr(target): todo.append(rom.off(target))
                if opcode in END_CMDS: break
                pc += length
        return WalkResult(gifts, finds, dynamic, visited)


# ------------------------------------------------------- script entries --
def iter_map_scripts(rom, map_header):
    """Yield (type, ROM offset) for each entry of a map's map-scripts list."""
    map_scripts = rom.u32(map_header + MAP_HEADER_SCRIPTS)
    if not rom.isptr(map_scripts): return
    map_scripts = rom.off(map_scripts)
    for k in range(MAX_MAP_SCRIPTS):
        entry = map_scripts + MAP_SCRIPT_ENTRY_SIZE * k
        script_type = rom.data[entry]
        if script_type == 0: break
        script_pointer = rom.u32(entry + MAP_SCRIPT_POINTER)
        if not rom.isptr(script_pointer): break
        yield script_type, rom.off(script_pointer)


def iter_map_script_table(rom, table):
    """Yield (var, value, script offset) for an ON_FRAME / ON_WARP_INTO_MAP table (script runs when var == value)."""
    for j in range(MAX_MAP_SCRIPT_TABLE_ENTRIES):
        entry = table + MAP_SCRIPT_TABLE_ENTRY_SIZE * j
        var_id = rom.u16(entry)
        if var_id == 0: break
        script = rom.u32(entry + MAP_SCRIPT_TABLE_SCRIPT)
        if rom.isptr(script): yield var_id, rom.u16(entry + MAP_SCRIPT_TABLE_VALUE), rom.off(script)


def collect_entries(rom, maps):
    """Every script entry point in the map events (MapEntry), plus hidden items (HiddenItem).
    kind is object / trigger / sign / mapscript (map scripts have no x/y)."""
    entries = []
    hidden = []
    script_use = Counter()
    for map_ref in maps:
        events = rom.u32(map_ref.header + MAP_HEADER_EVENTS)
        if rom.isptr(events):
            events = rom.off(events)
            object_count, warp_count, coord_count, bg_count = rom.data[events + MAP_EVENTS_COUNTS:events + MAP_EVENTS_OBJECTS]
            object_events = rom.u32(events + MAP_EVENTS_OBJECTS)
            coord_events = rom.u32(events + MAP_EVENTS_COORDS)
            bg_events = rom.u32(events + MAP_EVENTS_BGS)
            if rom.isptr(object_events):
                object_events = rom.off(object_events)
                for i in range(object_count):
                    event_offset = object_events + OBJECT_EVENT_SIZE * i
                    x, y = struct.unpack_from("<hh", rom.data, event_offset + OBJECT_EVENT_POSITION)
                    script = rom.u32(event_offset + OBJECT_EVENT_SCRIPT)
                    if rom.isptr(script):
                        script_use[rom.off(script)] += 1
                        entries.append(MapEntry(rom.off(script), map_ref, x, y, "object", event_offset))
            if rom.isptr(coord_events):
                coord_events = rom.off(coord_events)
                for i in range(coord_count):
                    event_offset = coord_events + COORD_EVENT_SIZE * i
                    x, y = struct.unpack_from("<HH", rom.data, event_offset)
                    script = rom.u32(event_offset + COORD_EVENT_SCRIPT)
                    if rom.isptr(script): entries.append(MapEntry(rom.off(script), map_ref, x, y, "trigger", event_offset))
            if rom.isptr(bg_events):
                bg_events = rom.off(bg_events)
                for i in range(bg_count):
                    event_offset = bg_events + BG_EVENT_SIZE * i
                    x, y = struct.unpack_from("<HH", rom.data, event_offset)
                    kind = rom.data[event_offset + BG_EVENT_KIND]
                    if kind == BG_HIDDEN_ITEM:
                        item = rom.u16(event_offset + BG_EVENT_HIDDEN_ITEM)
                        hidden_item_id = rom.data[event_offset + BG_EVENT_HIDDEN_ITEM_ID]
                        quantity_byte = rom.data[event_offset + BG_EVENT_HIDDEN_ITEM_QUANTITY]
                        hidden.append(HiddenItem(map_ref, x, y, item, (quantity_byte & HIDDEN_ITEM_QUANTITY_MASK) or 1,
                                                 hidden_item_id, quantity_byte >> HIDDEN_ITEM_UNDERFOOT_BIT))
                    elif kind <= BG_EVENT_LAST_SCRIPT_KIND:
                        script = rom.u32(event_offset + BG_EVENT_SCRIPT)
                        if rom.isptr(script): entries.append(MapEntry(rom.off(script), map_ref, x, y, "sign", event_offset))
        # map scripts (on load / on frame / ...): no coordinates
        for script_type, script_pointer in iter_map_scripts(rom, map_ref.header):
            if script_type in (MAP_SCRIPT_ON_FRAME_TABLE, MAP_SCRIPT_ON_WARP_INTO_MAP_TABLE):
                for var_id, value, script in iter_map_script_table(rom, script_pointer):
                    entries.append(MapEntry(script, map_ref, "", "", "mapscript", None))
            else:
                entries.append(MapEntry(script_pointer, map_ref, "", "", "mapscript", None))

    return entries, hidden, script_use


# ------------------------------------------------------------------- main --
def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    here = os.path.dirname(os.path.abspath(__file__))
    parser.add_argument("rom", nargs="?", default=os.path.join(here, "input", "game.gba"))
    parser.add_argument("-o", "--output", default=os.path.join(here, "output", "items.csv"))
    parser.add_argument("--map-groups", type=lambda text: int(text, 0))
    parser.add_argument("--region-map-entries", type=lambda text: int(text, 0))
    parser.add_argument("--no-orphans", action="store_true", help="drop 'gift?' rows")
    args = parser.parse_args()
    log = lambda *parts: print(*parts, file=sys.stderr)

    rom = Rom(args.rom)
    items_base, istride, icount, item_name = find_items(rom)
    log("gItemsInfo        @ 0x%X  (%d items, %d bytes each)" % (items_base, icount, istride))
    map_groups = args.map_groups
    if map_groups is None: map_groups, _ = find_map_groups(rom)
    rme = args.region_map_entries if args.region_map_entries is not None else find_region_map_entries(rom)
    names = mapsec_names(rom, rme) if rme is not None else []
    log("gMapGroups        @ 0x%X" % map_groups)
    log("gRegionMapEntries @ %s (%d names)" % (hex(rme) if rme is not None else "-", len(names)))

    maps = list(iter_maps(rom, map_groups))
    log("maps              : %d" % len(maps))

    def route(map_header):
        sec = rom.data[map_header + MAP_HEADER_REGION_MAP_SECTION]
        return names[sec] if sec < len(names) and names[sec] else "MAPSEC_%d" % sec

    entries, hidden, script_use = collect_entries(rom, maps)

    # --- walk scripts
    native_args = learn_native_args(rom, sorted({entry.script for entry in entries}))
    log("callnatives       : %d, %d with inline arguments" % (len(native_args), sum(1 for arg_bytes in native_args.values() if arg_bytes)))
    walker = Walker(rom, native_args)
    rows, reached = [], set()
    cache = {}
    for script, (map_group, map_num, map_header), x, y, kind, event_offset in entries:
        if script not in cache: cache[script] = walker.walk(script)
        gifts, finds, dynamic, visited = cache[script]
        reached |= visited
        base = [route(map_header), "%d.%d" % (map_group, map_num), x, y]
        if kind == "object" and dynamic and rom.u16(event_offset + OBJECT_EVENT_TRAINER_RANGE):
            # expansion item ball: item in trainerRange_berryTreeId, amount in movementRangeX
            item = rom.u16(event_offset + OBJECT_EVENT_TRAINER_RANGE)
            qty = (rom.data[event_offset + OBJECT_EVENT_MOVEMENT_RANGE] & ITEM_BALL_QUANTITY_MASK) or 1
            flag = rom.u16(event_offset + OBJECT_EVENT_FLAG)
            rows.append(base + ["itemBall", item_name(item), qty, "0x%X" % flag, "0x%X" % (script + ROM_BASE)])
            continue
        flag = "0x%X" % rom.u16(event_offset + OBJECT_EVENT_FLAG) if kind == "object" else ""
        for item, qty, pc in finds:
            src = "itemBall" if kind == "object" and script_use[script] == 1 else "found"
            rows.append(base + [src, item_name(item), qty, flag, "0x%X" % (pc + ROM_BASE)])
        for item, qty, pc in gifts:
            rows.append(base + ["gift", item_name(item), qty, "", "0x%X" % (pc + ROM_BASE)])

    for (map_group, map_num, map_header), x, y, item, qty, hid, underfoot in hidden:
        rows.append([route(map_header), "%d.%d" % (map_group, map_num), x, y, "hidden", item_name(item), qty,
                     "hidden#%d" % hid, "", "underfoot" if underfoot else ""])

    # --- giveitem patterns the walker never reached
    if not args.no_orphans:
        anchors = sorted((script, mid) for script, mid, *_ in entries)
        import bisect
        keys = [address for address, _ in anchors]
        for match in GIVEITEM_RE.finditer(rom.data):
            pc = match.start() + GIVEITEM_CALLSTD_AT
            if pc in reached: continue
            item = int.from_bytes(match.group("item"), "little"); qty = int.from_bytes(match.group("amount"), "little")
            if item >= VARS_START: continue
            i = bisect.bisect_right(keys, pc) - 1
            if i < 0 or pc - keys[i] > MAX_SCRIPT_DISTANCE: route_name, mid = "unknown", ""
            else:
                _, (map_group, map_num, map_header) = anchors[i]
                route_name, mid = route(map_header), "%d.%d" % (map_group, map_num)
            src = "gift?" if ord(match.group("std")) == STD_OBTAIN_ITEM else "found?"
            rows.append([route_name, mid, "", "", src, item_name(item), qty if qty < VARS_START else "var",
                         "", "0x%X" % (pc + ROM_BASE)])

    uniq, seen_rows = [], set()
    for row in rows:
        row_key = tuple(row)
        if row_key not in seen_rows: seen_rows.add(row_key); uniq.append(row)
    rows = uniq

    os.makedirs(os.path.dirname(os.path.abspath(args.output)), exist_ok=True)
    with open(args.output, "w", newline="", encoding="utf-8") as csv_file:
        writer = csv.writer(csv_file)
        writer.writerow(ITEM_COLUMNS)
        writer.writerows(rows)
    source_counts = Counter(row[ITEM_COLUMNS.index("source")] for row in rows)
    log("wrote %d rows -> %s  %s" % (len(rows), args.output, dict(source_counts)))


if __name__ == "__main__":
    main()
