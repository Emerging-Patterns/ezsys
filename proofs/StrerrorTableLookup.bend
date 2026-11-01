# proofs of laws/StrerrorTableLookup.bend
import Base
import ../src/errno.bend as Err
import ../laws/StrerrorTableLookup.bend as Laws

# --- errors ---

def Laws.err_table(_code, _why):
  {==}

def Laws.look_none(_code, _why):
  {==}

def Laws.look_hit(k, text, rest, code, why, e):
  %Equal.sym(Bool, U32.is_eq(code, k), True{}, e)
    : {Err.err.when(_, _u => text, _u => Err.err.look(rest, code, why))
      == text : String}
  {==}

def Laws.look_miss(k, text, rest, code, why, e):
  %Equal.sym(Bool, U32.is_eq(code, k), False{}, e)
    : {Err.err.when(_, _u => text, _u => Err.err.look(rest, code, why))
      == Err.err.look(rest, code, why) : String}
  {==}
