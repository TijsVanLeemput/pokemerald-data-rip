# encounter-data-rip

Python scripts that pull wild encounters and item locations out of a
pokeemerald-expansion based ROM hack and write them to CSV.

- `extract_encounters.py` writes `output/encounters.csv`
- `extract_items.py` writes `output/items.csv`

They only use the Python standard library (Python 3.8+). They don't use fixed
addresses: every table is found by searching the ROM, so the scripts should keep
working after the hack is rebuilt and its tables move.

## Quick start

```bash
# put the ROM at input/game.gba, then:
python3 extract_encounters.py
python3 extract_items.py
```

Both scripts accept a different ROM path and output file:

```bash
python3 extract_encounters.py path/to/rom.gba -o out/encounters.csv
python3 extract_items.py      path/to/rom.gba -o out/items.csv
```

While running, each script prints the addresses of the tables it found (to
stderr). Run either script with `--help` to see every option.

`extract_items.py` imports helpers from `extract_encounters.py`, so keep both
files in the same folder.

## Supported ROMs

The scripts are built for and tested on **pokeemerald-expansion** builds. The
current `input/game.gba` is expansion 1.13.2, with 1525 species and 831 items.
They need the expansion ROM headers to find the species and item tables, so
they don't work on an unmodified Emerald ROM.

---

## encounters.csv

| column | meaning |
|---|---|
| `route` | location name from the hack's region map. When several maps share a name, the map id is added, e.g. `Challenger Rd. (1.85)`. A map with several encounter sets gets ` [set N]`. |
| `encounterType` | `land`, `water`, `rockSmash`, `oldRod`, `goodRod`, `superRod` (and `hidden` if the hack uses it) |
| `day/night` | `morning` / `day` / `evening` / `night`, or `any` when the map has no time-of-day encounters |
| `pokemonName` | species name |
| `encounterRate` | percent chance of this species once an encounter of this type triggers. If a species fills several slots, their chances are added together, so each route + type + time group sums to 100. |
| `catchRate` | the species' catch rate (0–255) |

Options:

- `--per-slot`: one row per encounter slot instead of one row per species.
- `--wild-headers`, `--header-size`, `--species-info`, `--map-groups`,
  `--region-map-entries`, `--types-per-time`: force a table address or layout
  if auto-detection ever picks the wrong one. Values can be hex, e.g. `0xE73BA4`.

Slot odds are the vanilla ones (land 20/20/10/10/10/10/5/5/4/4/1/1, water and
rock smash 60/30/5/4/1, old rod 70/30, good rod 60/20/20, super rod
40/40/15/4/1). I checked them against this hack's code. If a future version
changes them, edit `SLOT_RATES` at the top of `extract_encounters.py`.

### Notes on the current ROM

- **No day/night encounters.** The ROM has room for separate morning, day,
  evening and night lists, but only the default list is filled, and the game's
  code ignores the time of day when picking an encounter. So every row says
  `any`.
- **Cape East (24.106) [set 1–8]:** this map has eight possible encounter
  tables, and a game variable (0x403E) decides which one is active.
- **Petal Pass [set 2]:** this map has a second encounter table, but the game
  always uses the first one, so set 2 never appears in play.
- The "rockSmash" lists contain Pineco and Silcoon, so the hack may use that
  slot for something like Headbutt. You can rename the label in `TYPE_ORDER`.

---

## items.csv

| column | meaning |
|---|---|
| `route` | location name from the hack's region map |
| `mapId` | `group.num`, so maps that share a name can be told apart |
| `x`, `y` | tile coordinates on that map, as stored in its event data (the same numbers Porymap shows) |
| `source` | see below |
| `itemName` | item name |
| `quantity` | amount given |
| `flag` | item balls: the object's pickup flag; hidden items: `hidden#N` (the hidden-item flag index) |
| `scriptAddress` | ROM address of the script that gives the item (for gifts and finds) |
| `notes` | `underfoot` for hidden items with that marker set |

| source | meaning |
|---|---|
| `itemBall` | visible item ball on the map |
| `hidden` | hidden item on a tile |
| `gift` | an NPC, sign, step-on trigger or map script gives the item; x/y is that NPC, sign or tile (empty for map scripts) |
| `found` | a script "finds" an item without being an item ball |
| `gift?` / `found?` | item-giving code found in the ROM that no map event points to. It's attributed to the nearest map by address, with no x/y. Most of these look like unused scripts. Leave them out with `--no-orphans`. |

Options: `--no-orphans`, `--map-groups`, `--region-map-entries`.

### Caveats

- **Repeated gift rows.** A script used in several places gets a row per place.
  For example, the Plane Ticket clerk appears in 22 maps, and a trigger that
  covers 5 tiles gives 5 rows.
- **Hidden-item quantities aren't verified.** Most read as 1. 21 read as 2, and
  six special ones (Air Balloon, Flat Key, three Daisy Flowers, one Rare Candy)
  read as 126/127 with `underfoot`. Treat those numbers with suspicion.
- **Not included:** shop stock, berry trees, and items handed out by native
  code instead of a script.
- To find gifts, the script follows the game's event scripts and needs to know
  how long each script command is. If a future build adds commands it doesn't
  know, more gifts will drop into the `gift?` bucket. Add the new commands to
  `CMD_LEN` in `extract_items.py`.

---

## Where things are in the current ROM

These are found automatically. They're listed here for reference, and in case
you need to pass one with an override flag.

| table | ROM offset | notes |
|---|---|---|
| `gSpeciesInfo` | `0x748C88` | 260 bytes per species; name at +0x2C, catch rate at +0x08 |
| `gItemsInfo` | `0x6FBCA8` | 44 bytes per item; name pointer at +0x14 |
| `gWildMonHeaders` | `0xE73BA4` | 190 headers × 100 bytes (4 time-of-day blocks × 6 pointers) |
| `gMapGroups` | `0xFA4FC4` | 34 groups, 722 valid maps |
| `gRegionMapEntries` | `0xCE597C` | 213 location names |
| Item-ball script | `0x83210C8` | item id in the object's `trainerRange_berryTreeId`, amount in `movementRangeX` |

## Layout

```
encounter-data-rip/
├── README.md
├── extract_encounters.py
├── extract_items.py
├── input/
│   └── game.gba
└── output/
    ├── encounters.csv
    └── items.csv
```
