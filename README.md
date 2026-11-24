# encounter-data-rip

Python scripts that pull wild encounters, item locations and quests out of a pokeemerald-expansion based ROM hack and write them to CSV.

- `extract_encounters.py` writes `output/encounters.csv`
- `extract_items.py` writes `output/items.csv`
- `extract_quests.py` writes `output/quests.csv` and `output/quest_events.csv`
- `extract_quest_steps.py` writes `output/quest_steps.md` / `.csv`, a generated walkthrough of every quest

They only use the Python standard library (Python 3.8+). They don't use fixed addresses: every table is found by searching the ROM, so the scripts should keep working after the hack is rebuilt and its tables move.

## Quick start

```bash
# put the ROM at input/game.gba, then:
python3 extract_encounters.py
python3 extract_items.py
python3 extract_quests.py
python3 extract_quest_steps.py
```

Each script accepts a different ROM path and output file:

```bash
python3 extract_encounters.py path/to/rom.gba -o out/encounters.csv
python3 extract_items.py      path/to/rom.gba -o out/items.csv
```

While running, each script prints the addresses of the tables it found (to stderr). Run either script with `--help` to see every option.

`extract_items.py` imports helpers from `extract_encounters.py`, `extract_quests.py` imports from both, and `extract_quest_steps.py` imports from all three, so keep the files in the same folder.

## Supported ROMs

The scripts are built for and tested on **pokeemerald-expansion** builds.
They need the expansion ROM headers to find the species and item tables, so they don't work on an unmodified Emerald ROM.

Notes on a specific ROM (table addresses, quirks, hack-specific script commands) live
in `internal_docs/`, e.g. `internal_docs/ceruleum_edition.md`.

---

## encounters.csv

| column          | meaning                                                                                                                                                                                    |
| --------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `route`         | location name from the hack's region map. When several maps share a name, the map id is added, e.g. `Challenger Rd. (1.85)`. A map with several encounter sets gets `[set N]`.             |
| `encounterType` | `land`, `water`, `rockSmash`, `oldRod`, `goodRod`, `superRod` (and `hidden` if the hack uses it)                                                                                           |
| `day/night`     | `morning` / `day` / `evening` / `night`, or `any` when the map has no time-of-day encounters                                                                                               |
| `pokemonName`   | species name                                                                                                                                                                               |
| `encounterRate` | percent chance of this species once an encounter of this type triggers. If a species fills several slots, their chances are added together, so each route + type + time group sums to 100. |
| `catchRate`     | the species' catch rate (0–255)                                                                                                                                                            |

Options:

- `--per-slot`: one row per encounter slot instead of one row per species.
- `--wild-headers`, `--header-size`, `--species-info`, `--map-groups`, `--region-map-entries`, `--types-per-time`: force a table address or layout if auto-detection ever picks the wrong one. Values can be hex, e.g. `0xE73BA4`.

Slot odds are the vanilla ones:

- Land: 20/20/10/10/10/10/5/5/4/4/1/1
- Water and rock smash 60/30/5/4/1
- Old rod 70/30,
- Good rod 60/20/20,
- Super rod 40/40/15/4/1

If a hack changes them, edit `SLOT_RATES` at the top of `extract_encounters.py`.
The encounter type labels are in `TYPE_ORDER`.

---

## items.csv

| column          | meaning                                                                                     |
| --------------- | ------------------------------------------------------------------------------------------- |
| `route`         | location name from the hack's region map                                                    |
| `mapId`         | `group.num`, so maps that share a name can be told apart                                    |
| `x`, `y`        | tile coordinates on that map, as stored in its event data (the same numbers Porymap shows)  |
| `source`        | see below                                                                                   |
| `itemName`      | item name                                                                                   |
| `quantity`      | amount given                                                                                |
| `flag`          | item balls: the object's pickup flag; hidden items: `hidden#N` (the hidden-item flag index) |
| `scriptAddress` | ROM address of the script that gives the item (for gifts and finds)                         |
| `notes`         | `underfoot` for hidden items with that marker set                                           |

| source             | meaning                                                                                                                                                                                                |
| ------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `itemBall`         | visible item ball on the map                                                                                                                                                                           |
| `hidden`           | hidden item on a tile                                                                                                                                                                                  |
| `gift`             | an NPC, sign, step-on trigger or map script gives the item; x/y is that NPC, sign or tile (empty for map scripts)                                                                                      |
| `found`            | a script "finds" an item without being an item ball                                                                                                                                                    |
| `gift?` / `found?` | item-giving code found in the ROM that no map event points to. It's attributed to the nearest map by address, with no x/y. Most of these look like unused scripts. Leave them out with `--no-orphans`. |

Options: `--no-orphans`, `--map-groups`, `--region-map-entries`.

### Caveats

- **Repeated gift rows.** A script used in several places gets a row per place, and a trigger that covers 5 tiles gives 5 rows.
- **Hidden-item quantities aren't verified.** The quantity byte's encoding wasn't confirmed in code; values like 126/127 (with `underfoot`) are probably not literal quantities.
- **Not included:** shop stock, berry trees, and items handed out by native code instead of a script.
- To find gifts, the script follows the game's event scripts and needs to know how long each script command is. If a future build adds commands it doesn't know, more gifts will drop into the `gift?` bucket. Add the new commands to `CMD_LEN` in `extract_items.py`.

---

## quests.csv

For hacks that use PokemonSanFran's [Unbound Quest Menu](https://github.com/PokemonSanFran/pokeemerald/wiki/Unbound-Quest-Menu).
Its quest list is a C array (`sSideQuests`, one `struct SideQuest` of 28 bytes per quest: name, description, completed description, map name, sprite, sprite type, subquest pointer and count). The script finds it by scanning the ROM.

| column                                               | meaning                                                                                                                                                                                          |
| ---------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `questNumber`                                        | 1-based position in the quest menu (`QUEST_1` = 1)                                                                                                                                               |
| `questId`                                            | 0-based id the game uses in `questmenu` / `startquest`                                                                                                                                           |
| `name`                                               | quest name                                                                                                                                                                                       |
| `description`                                        | text shown while the quest is active (line breaks become spaces; `--keep-newlines` keeps them)                                                                                                   |
| `completedDescription`                               | text shown once it's done                                                                                                                                                                        |
| `location`                                           | the map name shown in the quest menu                                                                                                                                                             |
| `spriteType`                                         | `object` (overworld sprite), `object (pokemon)`, `item` or `pokemon`                                                                                                                             |
| `sprite`                                             | the sprite: species / item name, or for overworld sprites the pokeemerald-expansion `OBJ_EVENT_GFX_*` name (a hint only: the hack can redraw these), or `hack gfx #N` for sprites the hack added |
| `spriteId`                                           | raw sprite id                                                                                                                                                                                    |
| `subquests`                                          | number of subquests                                                                                                                                                                              |
| `unlockedAt`, `startedAt`, `rewardAt`, `completedAt` | maps whose scripts unlock / start / set to reward / complete the quest                                                                                                                           |

## quest_events.csv

One row per `questmenu` script command that changes or checks a quest: `questNumber`, `questName`, `action` (`unlock`, `start`, `reward`, `complete`, `check*`), `route`, `mapId`, `x`, `y`, `eventKind` (`object`, `sign`, `trigger`, `mapscript`) and `scriptAddress`.
Actions ending in `?` are `startquest`/`completequest` macros that no map event reaches by pointer. Like `gift?` items, they're attributed to the nearest map by address and have no x/y.

If the hack ever adds subquests, `subquests.csv` is written as well.

Options: `--quest-table`, `--quest-count`, `--questmenu-opcode`, `--map-groups`, `--region-map-entries`, `--keep-newlines`.

---

## Quest steps

`extract_quest_steps.py` writes a walkthrough of every quest, generated from the ROM: `output/quest_steps.md` (readable) and `output/quest_steps.csv` (one row per step: questNumber, questName, step, role, location, mapId, x, y, what, details, script).

```bash
python3 extract_items.py            # needed for "where to find" lines
python3 extract_encounters.py       # needed for "where to catch" lines
python3 extract_quest_steps.py      # all quests
python3 extract_quest_steps.py --quest 17
```

How it works:

- Every map script (NPCs, signs, step triggers, map scripts) is run symbolically. Each possible path through the script is followed, recording the conditions taken on the way and what the path does. Conditions include flag set, var == n, answered Yes, has item, time of day, menu choice and Pokémon in party. Actions include dialogue, battles, items or Pokémon given or taken, flags/vars changed, quest started or completed, warps and phone calls. Step triggers and frame map scripts also carry the var == value they need to fire.
- The paths that start or complete a quest define its state: the flags and vars they change or test. Any other path that changes that state in a way a quest step is waiting for becomes a step (repeated until nothing new is found).
- Steps are ordered by dependency: a step that sets var = 2 comes before one that needs var == 2. One that gives an item comes before one that needs it, and one that unhides an NPC comes before talking to that NPC. Steps a quest needs before it can start are shown as "Before starting".
- The main story variable is found automatically (the var with the most distinct values). Quests that run along the story list the story events between their start and completion. Story requirements read "after the story event in `<map>` (story step N)".
- Variants that only differ in small ways (nickname yes/no, standing position) are merged.

Known limits: menu options and trainer names come from the ROM's tables, found by search. Checks done by native code show as `(game check: special N passes)`.
Text the game builds at runtime (`{STR_VAR_1}`) isn't filled in.

### Script decoding notes

- Hacks add their own script commands. Their lengths go in `CMD_LEN` in `extract_items.py`; the `questmenu` opcode is detected automatically.
- Expansion implements many commands as `callnative Func` followed by inline arguments (givemon, checkspecies, getobjectxy, createfollowernpc...). The ROM doesn't say how many bytes each one takes, so `extract_items.py` works it out from each native function's code (calls to ScriptReadHalfword/ScriptReadWord and inline byte reads) and checks the guess against the call sites. `givemon`/`createmon` is variable length and is handled separately. Without this the script walker stops early in many scripts.

---

## Layout

```fs
encounter-data-rip/
├── README.md
├── extract_encounters.py
├── extract_items.py
├── extract_quests.py
├── extract_quest_steps.py
├── internal_docs/
│   └── ceruleum_edition.md   (notes on the current ROM)
├── input/
│   └── game.gba
└── output/
    ├── encounters.csv
    ├── items.csv
    ├── quests.csv
    ├── quest_events.csv
    └── quest_steps.md / quest_steps.csv
```
