# `text.split(s, O)` is Python's `s.split(O)`: the pieces between every `O`,
# scanning left to right as `text.replace` does, empty pieces kept: the empty
# text is one empty piece; for every `rest`, splitting `O ++ rest` is an empty
# piece before the pieces of `rest`; for every `h` and `t` where `O` does not
# start, splitting `h ++ t` puts `h` on the front of the first piece of `t`'s;
# there is always at least one piece. With an empty separator the answer is
# `[s]`, where Python raises `ValueError`.
import Base
import ../src/str.bend as Str

# LAW: the empty text is one empty piece
law split_end:
  for sh: Char
  for st: String
  {Str.text.split("", SCon{sh, st}) == [""] : List<&2, String>}

# LAW: a separator at the start ends an empty piece, and the scan goes on
# after it
law split_hit:
  for +sh: Char
  for +st: String
  for +rest: String
  {Str.text.split(SCon{sh, st} ++ rest, SCon{sh, st})
    == SNil{} <> Str.text.split(rest, SCon{sh, st}) : List<&2, String>}

# LAW: a character where no separator starts begins the first piece
law split_miss:
  for +h: Char
  for +t: String
  for +sh: Char
  for +st: String
  for e: {String.starts_with(SCon{h, t}, SCon{sh, st}) == False{} : Bool}
  {Str.text.split(SCon{h, t}, SCon{sh, st})
    == Str.text.split.push(h, Str.text.split(t, SCon{sh, st}))
    : List<&2, String>}

# LAW: a character pushed on the pieces goes on the front of the first
law split_push:
  for h: Char
  for p: String
  for ps: List<&2, String>
  {Str.text.split.push(h, p <> ps) == SCon{h, p} <> ps : List<&2, String>}

# LAW: split never answers no pieces
law split_some:
  for +s: String
  for +sh: Char
  for +st: String
  {List.is_empty(&2, String, Str.text.split(s, SCon{sh, st})) == False{}
    : Bool}

# LAW: an empty separator answers the text as its one piece
law split_whole:
  for s: String
  {Str.text.split(s, "") == [s] : List<&2, String>}
