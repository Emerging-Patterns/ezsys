# A table maps a code point to its entry's text when it has a multiple mapping
# (the first entry for it), and otherwise to the one code point the first rule
# that covers it gives, or to itself when no rule does; a rule covers exactly
# the code points from `lo` to `hi` that are a multiple of `step` past `lo`,
# and maps `x` to `to + (x - lo)`.
import Base
import ../src/str.bend as Str

# LAW: a code point with a multiple mapping maps to its text
law case_multi:
  for ms: List<&2, Str.Multi>
  for rules: List<&2, Str.Rule>
  for +x: U32
  for s: String
  for e: {Str.text.case.multi(ms, x) == Some{s} : Maybe<&2, String>}
  {Str.text.case.of(ms, rules, x) == s : String}

# LAW: any other code point maps to the one code point the rules give
law case_rules:
  for ms: List<&2, Str.Multi>
  for rules: List<&2, Str.Rule>
  for +x: U32
  for e: {Str.text.case.multi(ms, x) == None{} : Maybe<&2, String>}
  {Str.text.case.of(ms, rules, x)
    == SCon{Chr{Str.text.case.apply(rules, x)}, SNil{}} : String}

# LAW: no entry holds no multiple mapping
law multi_none:
  for x: U32
  {Str.text.case.multi([], x) == None{} : Maybe<&2, String>}

# LAW: the first entry for a code point gives its text
law multi_hit:
  for +from: U32
  for to: String
  for rest: List<&2, Str.Multi>
  for +x: U32
  for e: {U32.is_eq(from, x) == True{} : Bool}
  {Str.text.case.multi(Str.Multi{from, to} <> rest, x) == Some{to}
    : Maybe<&2, String>}

# LAW: an entry for another code point is passed over
law multi_miss:
  for +from: U32
  for to: String
  for rest: List<&2, Str.Multi>
  for +x: U32
  for e: {U32.is_eq(from, x) == False{} : Bool}
  {Str.text.case.multi(Str.Multi{from, to} <> rest, x)
    == Str.text.case.multi(rest, x) : Maybe<&2, String>}

# LAW: no rule leaves a code point as it is
law apply_none:
  for x: U32
  {Str.text.case.apply([], x) == x : U32}

# LAW: the first rule that covers a code point maps it
law apply_hit:
  for +r: Str.Rule
  for rest: List<&2, Str.Rule>
  for +x: U32
  for e: {Str.text.case.covers(r, x) == True{} : Bool}
  {Str.text.case.apply(r <> rest, x) == Str.text.case.target(r, x) : U32}

# LAW: a rule that does not cover a code point is passed over
law apply_miss:
  for +r: Str.Rule
  for rest: List<&2, Str.Rule>
  for +x: U32
  for e: {Str.text.case.covers(r, x) == False{} : Bool}
  {Str.text.case.apply(r <> rest, x) == Str.text.case.apply(rest, x) : U32}

# LAW: a rule covers the code points from lo to hi, every step-th from lo
law covers_def:
  for +lo: U32
  for +hi: U32
  for +step: U32
  for to: U32
  for +x: U32
  {Str.text.case.covers(Str.Rule{lo, hi, step, to}, x)
    == Bool.and(Bool.and(U32.is_ge(x, lo), U32.is_le(x, hi)),
      U32.is_eq(((x - lo) % step : U32), 0)) : Bool}

# LAW: a rule maps lo to `to`, and each code point after it as far on
law target_def:
  for +lo: U32
  for hi: U32
  for step: U32
  for +to: U32
  for +x: U32
  {Str.text.case.target(Str.Rule{lo, hi, step, to}, x) == (to + (x - lo) : U32)
    : U32}
