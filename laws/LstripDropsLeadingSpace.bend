# `text.lstrip` is Python's `str.lstrip()`: for every character `h` and text
# `t`, `text.lstrip(h ++ t)` is `text.lstrip(t)` when `h` is whitespace and `h
# ++ t` otherwise, and the empty text is kept.
import Base
import ../src/str.bend as Str

# LAW: a leading whitespace character is removed, and lstrip goes on
law lstrip_space:
  for h: Char
  for t: String
  for e: {Str.text.space(h) == True{} : Bool}
  {Str.text.lstrip(SCon{h, t}) == Str.text.lstrip(t) : String}

# LAW: a text that starts with a character that is not whitespace is kept
law lstrip_keep:
  for h: Char
  for t: String
  for e: {Str.text.space(h) == False{} : Bool}
  {Str.text.lstrip(SCon{h, t}) == SCon{h, t} : String}

# LAW: the empty text is kept
law lstrip_empty:
  for s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {Str.text.lstrip(s) == s : String}
