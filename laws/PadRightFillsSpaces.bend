# For every text `s` and count `n`, `text.pad_right(s, n)` is Python's
# `s.ljust(n)`: `s` followed by U+0020 for every code point it is short of
# `n`, so it is `n` code points long, or as long as `s` when `s` is longer.
import Base
import ../src/str.bend as Str

# --- width ---

# LAW: pad_right writes the text, then a space for every code point it is
# short of n
law pad_form:
  for +s: String
  for +n: Nat
  {Str.text.pad_right(s, n)
    == s ++ String.repeat(" ", Nat.sub(n, String.length(s))) : String}

# LAW: pad_right is n code points long, or the text's length when it is
# longer
law pad_length:
  for +s: String
  for +n: Nat
  {String.length(Str.text.pad_right(s, n)) == Nat.max(String.length(s), n)
    : Nat}
