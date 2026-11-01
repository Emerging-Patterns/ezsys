# For every text `s` and count `n`, `text.truncate(s, n)` is Python's `s[:n]`:
# the text that `String.drop(s, n)` follows to make `s`, `n` code points long,
# or as long as `s` when `s` is shorter.
import Base
import ../src/str.bend as Str

# LAW: truncate is the text's first part: the rest after it gives the text
# back
law trunc_split:
  for +s: String
  for +n: Nat
  {Str.text.truncate(s, n) ++ String.drop(s, n) == s : String}

# LAW: truncate is n code points long, or the text's length when it is
# shorter
law trunc_length:
  for +s: String
  for +n: Nat
  {String.length(Str.text.truncate(s, n)) == Nat.min(String.length(s), n)
    : Nat}
