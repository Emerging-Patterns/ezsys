# proofs of laws/FindGivesFirstIndex.bend
import Base
import ../src/str.bend as Str
import ../laws/FindGivesFirstIndex.bend as Laws

def Laws.find_empty(s):
  match s:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

def Laws.find_hit(h, t, needle, e):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, needle), True{}, e)
    : {Str.text.find.at(_, _u => Str.text.find(t, needle)) == Some{0}
      : Maybe<&2, U32>}
  {==}

def Laws.find_next(h, t, needle, i, e, got):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, needle), False{}, e)
    : {Str.text.find.at(_, _u => Str.text.find(t, needle))
      == Some{(i + 1 : U32)} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, Str.text.find(t, needle), Some{i}, got)
    : {Str.text.find.inc(_) == Some{(i + 1 : U32)} : Maybe<&2, U32>}
  {==}

def Laws.find_none(h, t, needle, e, got):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, needle), False{}, e)
    : {Str.text.find.at(_, _u => Str.text.find(t, needle)) == None{}
      : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, Str.text.find(t, needle), None{}, got)
    : {Str.text.find.inc(_) == None{} : Maybe<&2, U32>}
  {==}

def Laws.find_end(_nh, _nt):
  {==}
