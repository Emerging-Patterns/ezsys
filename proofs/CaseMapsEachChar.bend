# proofs of laws/CaseMapsEachChar.bend
import Base
import ../src/str.bend as Str
import ../laws/CaseMapsEachChar.bend as Laws
import ./lemmas/BoolFacts.bend as M1

# --- case ---

def Laws.lower_con(_h, _t):
  {==}

def Laws.lower_nil(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      M1.no({Str.text.lower(SCon{h, t}) == SCon{h, t} : String}, e)

def Laws.upper_con(_h, _t):
  {==}

def Laws.upper_nil(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      M1.no({Str.text.upper(SCon{h, t}) == SCon{h, t} : String}, e)
