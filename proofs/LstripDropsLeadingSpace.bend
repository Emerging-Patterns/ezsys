# proofs of laws/LstripDropsLeadingSpace.bend
import Base
import ../src/str.bend as Str
import ../laws/LstripDropsLeadingSpace.bend as Laws
import ./lemmas/BoolFacts.bend as M1

def Laws.lstrip_space(h, t, e):
  %Equal.sym(Bool, Str.text.space(h), True{}, e)
    : {Str.text.lstrip.if(_, h, t, _u => Str.text.lstrip(t))
      == Str.text.lstrip(t) : String}
  {==}

def Laws.lstrip_keep(h, t, e):
  %Equal.sym(Bool, Str.text.space(h), False{}, e)
    : {Str.text.lstrip.if(_, h, t, _u => Str.text.lstrip(t)) == SCon{h, t}
      : String}
  {==}

def Laws.lstrip_empty(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      M1.no({Str.text.lstrip(SCon{h, t}) == SCon{h, t} : String}, e)
