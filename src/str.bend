# ezsys/src/str: text helpers that Python's str gives a service for free:
# strip with Python's whitespace, replace, split and find on a text
# separator, lower and upper case for ASCII, Latin-1, Latin Extended-A,
# Greek and Cyrillic, padding and truncation by code point, and the numeric
# order of digit strings. Pure; every function walks its text once, left to
# right, one code point a step.
import Base

# --- whitespace ---

# Python's whitespace (str.isspace, str.strip with no argument): the code
# points 9 to 13, 28 to 32, 133, 160, 5760, 8192 to 8202, 8232, 8233, 8239,
# 8287 and 12288
def text.spaces() -> List<&2, U32>:
  [9, 10, 11, 12, 13, 28, 29, 30, 31, 32, 133, 160, 5760, 8192, 8193, 8194,
    8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8232, 8233, 8239, 8287,
    12288]

# whether a character is Python whitespace
def text.space(chr: Char) -> Bool:
  match chr:
    case Chr{+x}:
      List.contains(~U32, ~U32.is_eq, text.spaces(), x)

# a character at the start: dropped when it is whitespace, and the rest
# stripped too; else the text is kept from it
def text.lstrip.if(
  sp: Bool,
  hd: Char,
  tl: String,
  more: Unit -> String
) -> String:
  match sp:
    case True{}:
      more(Unit{})
    case False{}:
      SCon{hd, tl}

# the text with its leading whitespace removed
def text.lstrip(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{+h, +t}:
      text.lstrip.if(text.space(h), h, t, _u => text.lstrip(t))

# a lone last character: gone when it is whitespace
def text.rstrip.lone(sp: Bool, hd: Char) -> String:
  match sp:
    case True{}:
      SNil{}
    case False{}:
      SCon{hd, SNil{}}

# a character before the stripped rest: when nothing is left after it, it
# goes too if it is whitespace
def text.rstrip.put(+hd: Char, rule: String) -> String:
  match rule:
    case SNil{}:
      text.rstrip.lone(text.space(hd), hd)
    case SCon{a, b}:
      SCon{hd, SCon{a, b}}

# the text with its trailing whitespace removed
def text.rstrip(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      text.rstrip.put(h, text.rstrip(t))

# the text with whitespace removed from both ends
def text.strip(txt: String) -> String:
  text.rstrip(text.lstrip(txt))

# --- replace ---

# how many characters of a separator follow its first
def text.after(sep: String) -> Nat:
  match sep:
    case SNil{}:
      0n
    case SCon{_h, t}:
      String.length(t)

# a nonempty `old` at this character, or not: write `new` and pass over
# the rest of `old`, or write the character
def text.replace.at(
  hit: Bool,
  hd: Char,
  +new: String,
  +left: Nat,
  next: Nat -> String
) -> String:
  match hit:
    case True{}:
      new ++ next(left)
    case False{}:
      SCon{hd, next(0n)}

# the scan for a nonempty `old`; `skip` characters of a found `old` are
# still to pass over
def text.replace.go(
  txt: String,
  skip: Nat,
  +old: String,
  +new: String
) -> String:
  match txt skip:
    case SNil{} _:
      SNil{}
    case SCon{_h, t} 1n+k:
      text.replace.go(t, k, old, new)
    case SCon{+h, +t} 0n:
      text.replace.at(String.starts_with(SCon{h, t}, old), h, new,
        text.after(old),
        k => text.replace.go(t, k, old, new))

# an empty `old`: `new` after every character
def text.replace.gaps(txt: String, +new: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      SCon{h, new ++ text.replace.gaps(t, new)}

# every `old` replaced by `new`, left to right, never overlapping; an empty
# `old` puts `new` before every character and at the end
def text.replace(txt: String, +old: String, +new: String) -> String:
  match old:
    case SNil{}:
      new ++ text.replace.gaps(txt, new)
    case SCon{oh, ot}:
      text.replace.go(txt, 0n, SCon{oh, ot}, new)

# --- split ---

# a character on the front of the first piece
def text.split.push(hd: Char, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      [SCon{hd, SNil{}}]
    case p <> rest:
      SCon{hd, p} <> rest

# a separator at this character ends a piece; else the character starts it
def text.split.at(
  hit: Bool,
  hd: Char,
  +left: Nat,
  next: Nat -> List<&2, String>
) -> List<&2, String>:
  match hit:
    case True{}:
      SNil{} <> next(left)
    case False{}:
      text.split.push(hd, next(0n))

# the scan for a nonempty separator; `skip` characters of a found separator
# are still to pass over
def text.split.go(txt: String, skip: Nat, +sep: String) -> List<&2, String>:
  match txt skip:
    case SNil{} _:
      [SNil{}]
    case SCon{_h, t} 1n+k:
      text.split.go(t, k, sep)
    case SCon{+h, +t} 0n:
      text.split.at(String.starts_with(SCon{h, t}, sep), h,
        text.after(sep),
        k => text.split.go(t, k, sep))

# the pieces between the separators, in order; an empty separator splits
# nothing
def text.split(txt: String, +sep: String) -> List<&2, String>:
  match sep:
    case SNil{}:
      [txt]
    case SCon{sh, st}:
      text.split.go(txt, 0n, SCon{sh, st})

# --- find ---

# a place one character further on
def text.find.inc(got: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match got:
    case None{}:
      None{}
    case Some{+i}:
      Some{(i + 1 : U32)}

# the needle here, or further on
def text.find.at(here: Bool, rest: Unit -> Maybe<&2, U32>) -> Maybe<&2, U32>:
  match here:
    case True{}:
      Some{0}
    case False{}:
      text.find.inc(rest(Unit{}))

# at the end of the text only an empty needle is found
def text.find.end(needle: String) -> Maybe<&2, U32>:
  match needle:
    case SNil{}:
      Some{0}
    case SCon{_h, _t}:
      None{}

# the index, in code points, of the first place the needle starts
def text.find(txt: String, +needle: String) -> Maybe<&2, U32>:
  match txt:
    case SNil{}:
      text.find.end(needle)
    case SCon{+h, +t}:
      text.find.at(String.starts_with(SCon{h, t}, needle),
        _u => text.find(t, needle))

# --- case ---

# a run of code points `lo` to `hi`, every `step`-th one from `lo`, mapped
# in order onto the code points from `to`
type Rule is Data:
  Rule{lo: U32, hi: U32, step: U32, to: U32}

# a code point that maps to more than one
type Multi is Data:
  Multi{from: U32, to: String}

# whether a rule maps the code point
def text.case.covers(rule: Rule, +cp: U32) -> Bool:
  match rule:
    case Rule{+lo, +hi, +step, _to}:
      Bool.and(Bool.and(U32.is_ge(cp, lo), U32.is_le(cp, hi)),
        U32.is_eq(((cp - lo) % step : U32), 0))

# where a rule maps a code point it covers
def text.case.target(rule: Rule, +cp: U32) -> U32:
  match rule:
    case Rule{+lo, _hi, _step, +to}:
      (to + (cp - lo) : U32)

# the first rule's mapping, or the rest's
def text.case.pick(
  hit: Bool,
  +rule: Rule,
  +cp: U32,
  rest: Unit -> U32
) -> U32:
  match hit:
    case True{}:
      text.case.target(rule, cp)
    case False{}:
      rest(Unit{})

# the code point the first rule that covers it maps it to; itself when none
# does
def text.case.apply(rules: List<&2, Rule>, +cp: U32) -> U32:
  match rules:
    case Nil{}:
      cp
    case +r <> rest:
      text.case.pick(text.case.covers(r, cp), r, cp,
        _u => text.case.apply(rest, cp))

# this entry's text, or the rest's
def text.case.found(
  hit: Bool,
  to: String,
  rest: Unit -> Maybe<&2, String>
) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{to}
    case False{}:
      rest(Unit{})

# the text a code point that maps to more than one maps to
def text.case.multi(ms: List<&2, Multi>, +cp: U32) -> Maybe<&2, String>:
  match ms:
    case Nil{}:
      None{}
    case Multi{+from, +to} <> rest:
      text.case.found(U32.is_eq(from, cp), to,
        _u => text.case.multi(rest, cp))

# a multiple mapping's text, or the rules' one code point
def text.case.one(
  got: Maybe<&2, String>,
  +cp: U32,
  rules: List<&2, Rule>
) -> String:
  match got:
    case Some{s}:
      s
    case None{}:
      SCon{Chr{text.case.apply(rules, cp)}, SNil{}}

# a code point mapped by a table: its multiple mapping, else the rules
def text.case.of(
  ms: List<&2, Multi>,
  rules: List<&2, Rule>,
  +cp: U32
) -> String:
  text.case.one(text.case.multi(ms, cp), cp, rules)

# Unicode 13's lowercase mappings (Python's str.lower) of U+0000 to U+017F
# and U+0370 to U+04FF that are one code point
def text.lower.rules() -> List<&2, Rule>:
  [
    Rule{65, 90, 1, 97},
    Rule{192, 214, 1, 224},
    Rule{216, 222, 1, 248},
    Rule{256, 302, 2, 257},
    Rule{306, 310, 2, 307},
    Rule{313, 327, 2, 314},
    Rule{330, 374, 2, 331},
    Rule{376, 376, 1, 255},
    Rule{377, 381, 2, 378},
    Rule{880, 882, 2, 881},
    Rule{886, 886, 1, 887},
    Rule{895, 895, 1, 1011},
    Rule{902, 902, 1, 940},
    Rule{904, 906, 1, 941},
    Rule{908, 908, 1, 972},
    Rule{910, 911, 1, 973},
    Rule{913, 929, 1, 945},
    Rule{931, 939, 1, 963},
    Rule{975, 975, 1, 983},
    Rule{984, 1006, 2, 985},
    Rule{1012, 1012, 1, 952},
    Rule{1015, 1015, 1, 1016},
    Rule{1017, 1017, 1, 1010},
    Rule{1018, 1018, 1, 1019},
    Rule{1021, 1023, 1, 891},
    Rule{1024, 1039, 1, 1104},
    Rule{1040, 1071, 1, 1072},
    Rule{1120, 1152, 2, 1121},
    Rule{1162, 1214, 2, 1163},
    Rule{1216, 1216, 1, 1231},
    Rule{1217, 1229, 2, 1218},
    Rule{1232, 1278, 2, 1233}
  ]

# the lowercase mapping of U+0130 is two code points
def text.lower.multi() -> List<&2, Multi>:
  [Multi{304, "i\u{307}"}]

# Unicode 13's uppercase mappings (Python's str.upper) of U+0000 to U+017F
# and U+0370 to U+04FF that are one code point
def text.upper.rules() -> List<&2, Rule>:
  [
    Rule{97, 122, 1, 65},
    Rule{181, 181, 1, 924},
    Rule{224, 246, 1, 192},
    Rule{248, 254, 1, 216},
    Rule{255, 255, 1, 376},
    Rule{257, 303, 2, 256},
    Rule{305, 305, 1, 73},
    Rule{307, 311, 2, 306},
    Rule{314, 328, 2, 313},
    Rule{331, 375, 2, 330},
    Rule{378, 382, 2, 377},
    Rule{383, 383, 1, 83},
    Rule{881, 883, 2, 880},
    Rule{887, 887, 1, 886},
    Rule{891, 893, 1, 1021},
    Rule{940, 940, 1, 902},
    Rule{941, 943, 1, 904},
    Rule{945, 961, 1, 913},
    Rule{962, 962, 1, 931},
    Rule{963, 971, 1, 931},
    Rule{972, 972, 1, 908},
    Rule{973, 974, 1, 910},
    Rule{976, 976, 1, 914},
    Rule{977, 977, 1, 920},
    Rule{981, 981, 1, 934},
    Rule{982, 982, 1, 928},
    Rule{983, 983, 1, 975},
    Rule{985, 1007, 2, 984},
    Rule{1008, 1008, 1, 922},
    Rule{1009, 1009, 1, 929},
    Rule{1010, 1010, 1, 1017},
    Rule{1011, 1011, 1, 895},
    Rule{1013, 1013, 1, 917},
    Rule{1016, 1016, 1, 1015},
    Rule{1019, 1019, 1, 1018},
    Rule{1072, 1103, 1, 1040},
    Rule{1104, 1119, 1, 1024},
    Rule{1121, 1153, 2, 1120},
    Rule{1163, 1215, 2, 1162},
    Rule{1218, 1230, 2, 1217},
    Rule{1231, 1231, 1, 1216},
    Rule{1233, 1279, 2, 1232}
  ]

# the uppercase mappings of U+00DF, U+0149, U+0390 and U+03B0 are more than
# one code point
def text.upper.multi() -> List<&2, Multi>:
  [
    Multi{223, "SS"},
    Multi{329, "\u{2BC}N"},
    Multi{912, "\u{399}\u{308}\u{301}"},
    Multi{944, "\u{3A5}\u{308}\u{301}"}
  ]

# one character in lowercase
def text.lower.char(chr: Char) -> String:
  match chr:
    case Chr{+x}:
      text.case.of(text.lower.multi(), text.lower.rules(), x)

# one character in uppercase
def text.upper.char(chr: Char) -> String:
  match chr:
    case Chr{+x}:
      text.case.of(text.upper.multi(), text.upper.rules(), x)

# the text in lowercase, character by character
def text.lower(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      text.lower.char(h) ++ text.lower(t)

# the text in uppercase, character by character
def text.upper(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      text.upper.char(h) ++ text.upper(t)

# --- width ---

# the text with spaces after it up to `n` code points; a longer text is
# kept whole
def text.pad_right(txt: String, width: Nat) -> String:
  match txt width:
    case SNil{} k:
      String.repeat(" ", k)
    case SCon{h, t} 0n:
      SCon{h, t}
    case SCon{h, t} 1n+k:
      SCon{h, text.pad_right(t, k)}

# the first `n` code points of the text, or all of it when it is shorter
def text.truncate(txt: String, width: Nat) -> String:
  match txt width:
    case SNil{} _:
      SNil{}
    case SCon{_h, _t} 0n:
      SNil{}
    case SCon{h, t} 1n+k:
      SCon{h, text.truncate(t, k)}

# --- digit strings ---

# a leading '0' is dropped, and the zeros after it
def text.digits.zero.if(
  zero: Bool,
  hd: Char,
  tl: String,
  more: Unit -> String
) -> String:
  match zero:
    case True{}:
      more(Unit{})
    case False{}:
      SCon{hd, tl}

# the text with its leading '0's removed
def text.digits.trim(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{+h, +t}:
      text.digits.zero.if(Char.is_eq(h, '0'), h, t,
        _u => text.digits.trim(t))

# the longer text is the greater; texts of one length compare code point
# by code point
def text.digits.by(chr: Cmp, +lhs: String, +rhs: String) -> Cmp:
  match chr:
    case LT{}:
      LT{}
    case EQ{}:
      String.order(lhs, rhs)
    case GT{}:
      GT{}

# two digit strings in numeric order: leading zeros dropped, then the
# longer is the greater, and two of one length compare digit by digit
def text.digits.cmp(lhs: String, rhs: String) -> Cmp:
  +x = text.digits.trim(lhs)
  +y = text.digits.trim(rhs)
  text.digits.by(Nat.cmp(String.length(x), String.length(y)), x, y)
