# For every two texts, `text.digits.cmp` drops each one's leading `0`s (and
# keeps a text that starts with anything else, and the empty text), then
# answers `LT` when the first is shorter, `GT` when it is longer, and
# `String.order` of the two when they are one length.
#
# `text.digits.cmp(a, b)` compares two strings of ASCII digits in numeric
# order without reading them into a number, so any length works: what Python's
# `int(a)` and `int(b)` compare to, with the empty text counting as 0
# (pending, laws/DigitsCmpIsNumericOrder.bend). The rule it applies holds for
# every pair of texts, digits or not.
import Base
import ../src/str.bend as Str

# --- digit strings ---

# LAW: digits.cmp compares the texts without their leading zeros: the
# shorter is the lesser, and two of one length compare by String.order
law dig_rule:
  for a: String
  for b: String
  {Str.text.digits.cmp(a, b) == Str.text.digits.by(
    Nat.cmp(String.length(Str.text.digits.trim(a)),
      String.length(Str.text.digits.trim(b))),
    Str.text.digits.trim(a), Str.text.digits.trim(b)) : Cmp}

# LAW: a shorter text is the lesser
law dig_shorter:
  for a: String
  for b: String
  {Str.text.digits.by(LT{}, a, b) == LT{} : Cmp}

# LAW: a longer text is the greater
law dig_longer:
  for a: String
  for b: String
  {Str.text.digits.by(GT{}, a, b) == GT{} : Cmp}

# LAW: two texts of one length compare by String.order
law dig_same:
  for +a: String
  for +b: String
  {Str.text.digits.by(EQ{}, a, b) == String.order(a, b) : Cmp}

# LAW: a leading '0' is dropped, and trimming goes on
law trim_zero:
  for +t: String
  {Str.text.digits.trim(SCon{'0', t}) == Str.text.digits.trim(t) : String}

# LAW: a text that starts with anything but '0' is kept
law trim_keep:
  for +h: Char
  for +t: String
  for e: {Char.is_eq(h, '0') == False{} : Bool}
  {Str.text.digits.trim(SCon{h, t}) == SCon{h, t} : String}

# LAW: the empty text trims to itself
law trim_empty:
  for s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {Str.text.digits.trim(s) == s : String}
