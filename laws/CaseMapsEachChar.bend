# For every character `h` and text `t`, `text.lower(h ++ t)` is the lowercase
# of `h` followed by `text.lower(t)`, and the same for `text.upper`; both keep
# the empty text.
import Base
import ../src/str.bend as Str

# --- case ---

# LAW: lower is the lowercase of the first character, then of the rest
law lower_con:
  for h: Char
  for t: String
  {Str.text.lower(SCon{h, t}) == Str.text.lower.char(h) ++ Str.text.lower(t)
    : String}

# LAW: lower keeps the empty text
law lower_nil:
  for s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {Str.text.lower(s) == s : String}

# LAW: upper is the uppercase of the first character, then of the rest
law upper_con:
  for h: Char
  for t: String
  {Str.text.upper(SCon{h, t}) == Str.text.upper.char(h) ++ Str.text.upper(t)
    : String}

# LAW: upper keeps the empty text
law upper_nil:
  for s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {Str.text.upper(s) == s : String}
