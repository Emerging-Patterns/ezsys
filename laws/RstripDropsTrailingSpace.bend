# `text.rstrip` is Python's `str.rstrip()`: for every text `t` and character
# `h`, `text.rstrip(t ++ h)` is `text.rstrip(t)` when `h` is whitespace and `t
# ++ h` otherwise, and the empty text is kept; `text.strip(s)` is
# `text.rstrip(text.lstrip(s))`, Python's `str.strip()`.
import Base
import ../src/str.bend as Str

# LAW: a trailing whitespace character is removed, and rstrip goes on
law rstrip_space:
  for +t: String
  for +h: Char
  for e: {Str.text.space(h) == True{} : Bool}
  {Str.text.rstrip(t ++ SCon{h, SNil{}}) == Str.text.rstrip(t) : String}

# LAW: a text that ends with a character that is not whitespace is kept
law rstrip_keep:
  for +t: String
  for +h: Char
  for e: {Str.text.space(h) == False{} : Bool}
  {Str.text.rstrip(t ++ SCon{h, SNil{}}) == t ++ SCon{h, SNil{}} : String}

# LAW: the empty text is kept
law rstrip_empty:
  for s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {Str.text.rstrip(s) == s : String}

# LAW: strip is rstrip of lstrip
law strip_both:
  for s: String
  {Str.text.strip(s) == Str.text.rstrip(Str.text.lstrip(s)) : String}
