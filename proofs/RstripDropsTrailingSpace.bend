# proofs of laws/RstripDropsTrailingSpace.bend
import Base
import ../src/str.bend as Str
import ../laws/RstripDropsTrailingSpace.bend as Laws
import ./lemmas/BoolFacts.bend as M1

def Laws.rstrip_space(t, h, e):
  match t:
    case SNil{}:
      %Equal.sym(Bool, Str.text.space(h), True{}, e)
        : {Str.text.rstrip.lone(_, h) == SNil{} : String}
      {==}
    case SCon{+x, +r}:
      Equal.cong(String, String, y => Str.text.rstrip.put(x, y),
        Str.text.rstrip(r ++ SCon{h, SNil{}}), Str.text.rstrip(r),
        Laws.rstrip_space(r, h, e))

# a character before a nonempty rest is kept
law rstrip_put_con:
  for +x: Char
  for +r: String
  for +h: Char
  {Str.text.rstrip.put(x, r ++ SCon{h, SNil{}}) == SCon{x, r ++ SCon{h, SNil{}}}
    : String}

def rstrip_put_con(_x, r, _h):
  match r:
    case SNil{}:
      {==}
    case SCon{_a, _b}:
      {==}

def Laws.rstrip_keep(t, h, e):
  match t:
    case SNil{}:
      %Equal.sym(Bool, Str.text.space(h), False{}, e)
        : {Str.text.rstrip.lone(_, h) == SCon{h, SNil{}} : String}
      {==}
    case SCon{+x, +r}:
      Equal.trans(String,
        Str.text.rstrip.put(x, Str.text.rstrip(r ++ SCon{h, SNil{}})),
        Str.text.rstrip.put(x, r ++ SCon{h, SNil{}}),
        SCon{x, r ++ SCon{h, SNil{}}},
        Equal.cong(String, String, y => Str.text.rstrip.put(x, y),
          Str.text.rstrip(r ++ SCon{h, SNil{}}), r ++ SCon{h, SNil{}},
          Laws.rstrip_keep(r, h, e)),
        rstrip_put_con(x, r, h))

def Laws.rstrip_empty(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      M1.no({Str.text.rstrip(SCon{h, t}) == SCon{h, t} : String}, e)

def Laws.strip_both(_s):
  {==}
