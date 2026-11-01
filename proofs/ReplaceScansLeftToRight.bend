# proofs of laws/ReplaceScansLeftToRight.bend
import Base
import ../src/str.bend as Str
import ../laws/ReplaceScansLeftToRight.bend as Laws
import ./lemmas/TextScan.bend as M1

# --- replace, split and find ---

# the rest of a found `old` is passed over
law replace_skip:
  for +ot: String
  for +x: String
  for +old: String
  for +new: String
  {Str.text.replace.go(ot ++ x, String.length(ot), old, new)
    == Str.text.replace.go(x, 0n, old, new) : String}

def replace_skip(ot, x, old, new):
  match ot:
    case SNil{}:
      {==}
    case SCon{_c, +t}:
      replace_skip(t, x, old, new)

def Laws.replace_hit(oh, ot, rest, new):
  %Equal.sym(Bool, String.starts_with(SCon{oh, ot} ++ rest, SCon{oh, ot}),
    True{}, M1.starts_self(SCon{oh, ot}, rest))
    : {Str.text.replace.at(_, oh, new, String.length(ot),
      k => Str.text.replace.go(ot ++ rest, k, SCon{oh, ot}, new))
      == new ++ Str.text.replace.go(rest, 0n, SCon{oh, ot}, new) : String}
  Equal.cong(String, String, y => new ++ y,
    Str.text.replace.go(ot ++ rest, String.length(ot), SCon{oh, ot}, new),
    Str.text.replace.go(rest, 0n, SCon{oh, ot}, new),
    replace_skip(ot, rest, SCon{oh, ot}, new))

def Laws.replace_miss(h, t, oh, ot, new, e):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, SCon{oh, ot}), False{}, e)
    : {Str.text.replace.at(_, h, new, String.length(ot),
      k => Str.text.replace.go(t, k, SCon{oh, ot}, new))
      == SCon{h, Str.text.replace.go(t, 0n, SCon{oh, ot}, new)} : String}
  {==}

def Laws.replace_end(_oh, _ot, _new):
  {==}
