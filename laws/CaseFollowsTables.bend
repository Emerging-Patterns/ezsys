# For every code point, its lowercase and its uppercase are what the tables
# `lower_table` and `upper_table` below give.
#
# `text.lower` and `text.upper` are Python's `str.lower()` and `str.upper()`
# (Unicode 13's full case mappings, `SpecialCasing.txt` included) for the code
# points U+0000 to U+017F (ASCII, Latin-1 and Latin Extended-A) and U+0370 to
# U+04FF (Greek and Coptic, and Cyrillic), and leave every other code point as
# it is. The tables are Unicode's mapping of those code points written as
# runs: `Rule{lo, hi, step, to}` maps every `step`-th code point from `lo` to
# `hi` onto the code points from `to` in order, so `Rule{65, 90, 1, 97}` is
# `A` to `Z` onto `a` to `z` and `Rule{256, 302, 2, 257}` is Latin
# Extended-A's pairs. The special mappings to more than one code point are
# handled as Python does: lowercase U+0130 (`İ`) is U+0069 U+0307, and
# uppercase U+00DF (`ß`) is `SS`, U+0149 (`ŉ`) is U+02BC `N`, U+0390 is U+0399
# U+0308 U+0301 and U+03B0 is U+03A5 U+0308 U+0301.
#
# Outside the guarantee: Python writes a final sigma, U+03C2, for U+03A3 at
# the end of a word, which needs the cased and case-ignorable properties of
# every code point; `text.lower` always writes U+03C3. Python also maps code
# points outside the two ranges (Latin Extended-B, Latin Extended Additional,
# Armenian, Georgian, full-width and Deseret letters, U+1E9E, ligatures like
# U+FB01 and the like), which are left as they are here.
import Base
import ../src/str.bend as Str

# LAW: a character's lowercase is given by this table: U+0130 maps to
# U+0069 U+0307, and every rule maps a run of code points in order
law lower_table:
  for x: U32
  {Str.text.lower.char(Chr{x}) == Str.text.case.of(
    [Str.Multi{304, "i\u{307}"}],
    [
        Str.Rule{65, 90, 1, 97},
        Str.Rule{192, 214, 1, 224},
        Str.Rule{216, 222, 1, 248},
        Str.Rule{256, 302, 2, 257},
        Str.Rule{306, 310, 2, 307},
        Str.Rule{313, 327, 2, 314},
        Str.Rule{330, 374, 2, 331},
        Str.Rule{376, 376, 1, 255},
        Str.Rule{377, 381, 2, 378},
        Str.Rule{880, 882, 2, 881},
        Str.Rule{886, 886, 1, 887},
        Str.Rule{895, 895, 1, 1011},
        Str.Rule{902, 902, 1, 940},
        Str.Rule{904, 906, 1, 941},
        Str.Rule{908, 908, 1, 972},
        Str.Rule{910, 911, 1, 973},
        Str.Rule{913, 929, 1, 945},
        Str.Rule{931, 939, 1, 963},
        Str.Rule{975, 975, 1, 983},
        Str.Rule{984, 1006, 2, 985},
        Str.Rule{1012, 1012, 1, 952},
        Str.Rule{1015, 1015, 1, 1016},
        Str.Rule{1017, 1017, 1, 1010},
        Str.Rule{1018, 1018, 1, 1019},
        Str.Rule{1021, 1023, 1, 891},
        Str.Rule{1024, 1039, 1, 1104},
        Str.Rule{1040, 1071, 1, 1072},
        Str.Rule{1120, 1152, 2, 1121},
        Str.Rule{1162, 1214, 2, 1163},
        Str.Rule{1216, 1216, 1, 1231},
        Str.Rule{1217, 1229, 2, 1218},
        Str.Rule{1232, 1278, 2, 1233}
      ], x) : String}

# LAW: a character's uppercase is given by this table: U+00DF, U+0149,
# U+0390 and U+03B0 map to more than one code point, and every rule maps a
# run of code points in order
law upper_table:
  for x: U32
  {Str.text.upper.char(Chr{x}) == Str.text.case.of(
    [
        Str.Multi{223, "SS"},
        Str.Multi{329, "\u{2BC}N"},
        Str.Multi{912, "\u{399}\u{308}\u{301}"},
        Str.Multi{944, "\u{3A5}\u{308}\u{301}"}
      ],
    [
        Str.Rule{97, 122, 1, 65},
        Str.Rule{181, 181, 1, 924},
        Str.Rule{224, 246, 1, 192},
        Str.Rule{248, 254, 1, 216},
        Str.Rule{255, 255, 1, 376},
        Str.Rule{257, 303, 2, 256},
        Str.Rule{305, 305, 1, 73},
        Str.Rule{307, 311, 2, 306},
        Str.Rule{314, 328, 2, 313},
        Str.Rule{331, 375, 2, 330},
        Str.Rule{378, 382, 2, 377},
        Str.Rule{383, 383, 1, 83},
        Str.Rule{881, 883, 2, 880},
        Str.Rule{887, 887, 1, 886},
        Str.Rule{891, 893, 1, 1021},
        Str.Rule{940, 940, 1, 902},
        Str.Rule{941, 943, 1, 904},
        Str.Rule{945, 961, 1, 913},
        Str.Rule{962, 962, 1, 931},
        Str.Rule{963, 971, 1, 931},
        Str.Rule{972, 972, 1, 908},
        Str.Rule{973, 974, 1, 910},
        Str.Rule{976, 976, 1, 914},
        Str.Rule{977, 977, 1, 920},
        Str.Rule{981, 981, 1, 934},
        Str.Rule{982, 982, 1, 928},
        Str.Rule{983, 983, 1, 975},
        Str.Rule{985, 1007, 2, 984},
        Str.Rule{1008, 1008, 1, 922},
        Str.Rule{1009, 1009, 1, 929},
        Str.Rule{1010, 1010, 1, 1017},
        Str.Rule{1011, 1011, 1, 895},
        Str.Rule{1013, 1013, 1, 917},
        Str.Rule{1016, 1016, 1, 1015},
        Str.Rule{1019, 1019, 1, 1018},
        Str.Rule{1072, 1103, 1, 1040},
        Str.Rule{1104, 1119, 1, 1024},
        Str.Rule{1121, 1153, 2, 1120},
        Str.Rule{1163, 1215, 2, 1162},
        Str.Rule{1218, 1230, 2, 1217},
        Str.Rule{1231, 1231, 1, 1216},
        Str.Rule{1233, 1279, 2, 1232}
      ], x) : String}
