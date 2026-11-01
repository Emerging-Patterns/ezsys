# With an empty `old`, `text.replace(s, "", new)` is Python's `s.replace("",
# new)`: `new` before every character and at the end (`"ab"` gives `new a new
# b new`): for every `h` and `t`, it is `new ++ h` followed by replacing in
# `t`, and on the empty text it is `new`.
import Base
import ../src/str.bend as Str

# LAW: an empty `old` puts `new` before the first character, and goes on
law replace_gaps:
  for +h: Char
  for +t: String
  for +new: String
  {Str.text.replace(SCon{h, t}, "", new)
    == new ++ SCon{h, Str.text.replace(t, "", new)} : String}

# LAW: an empty `old` in the empty text gives `new`
law replace_gaps_end:
  for +new: String
  {Str.text.replace("", "", new) == new : String}
