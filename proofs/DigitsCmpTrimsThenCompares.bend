# proofs of laws/DigitsCmpTrimsThenCompares.bend
import Base
import ../src/str.bend as Str
import ../laws/DigitsCmpTrimsThenCompares.bend as Laws
import ./lemmas/BoolFacts.bend as M1

# --- digit strings ---

def Laws.dig_rule(_a, _b):
  {==}

def Laws.dig_shorter(_a, _b):
  {==}

def Laws.dig_longer(_a, _b):
  {==}

def Laws.dig_same(_a, _b):
  {==}

def Laws.trim_zero(_t):
  {==}

def Laws.trim_keep(h, t, e):
  %Equal.sym(Bool, Char.is_eq(h, '0'), False{}, e)
    : {Str.text.digits.zero.if(_, h, t, _u => Str.text.digits.trim(t))
      == SCon{h, t} : String}
  {==}

def Laws.trim_empty(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      M1.no({Str.text.digits.trim(SCon{h, t}) == SCon{h, t} : String}, e)
