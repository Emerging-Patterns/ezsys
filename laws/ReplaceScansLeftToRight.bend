# `text.replace(s, O, new)` is Python's `s.replace(O, new)`: every `O` is
# replaced, scanning left to right and going on after the `O` it replaced, so
# two never overlap (`"aaa"` with `"aa"` gives `new ++ "a"`): for every text
# `rest`, replacing in `O ++ rest` is `new` followed by replacing in `rest`;
# for every `h` and `t` where `O` does not start, replacing in `h ++ t` is `h`
# followed by replacing in `t`; and replacing in the empty text is the empty
# text.
import Base
import ../src/str.bend as Str

# --- replace, split and find ---

# LAW: an `old` at the start is replaced, and the scan goes on after it
law replace_hit:
  for +oh: Char
  for +ot: String
  for +rest: String
  for +new: String
  {Str.text.replace(SCon{oh, ot} ++ rest, SCon{oh, ot}, new)
    == new ++ Str.text.replace(rest, SCon{oh, ot}, new) : String}

# LAW: a character where no `old` starts is kept, and the scan goes on
# after it
law replace_miss:
  for +h: Char
  for +t: String
  for +oh: Char
  for +ot: String
  for +new: String
  for e: {String.starts_with(SCon{h, t}, SCon{oh, ot}) == False{} : Bool}
  {Str.text.replace(SCon{h, t}, SCon{oh, ot}, new)
    == SCon{h, Str.text.replace(t, SCon{oh, ot}, new)} : String}

# LAW: replacing in the empty text gives the empty text
law replace_end:
  for oh: Char
  for ot: String
  for new: String
  {Str.text.replace("", SCon{oh, ot}, new) == "" : String}
