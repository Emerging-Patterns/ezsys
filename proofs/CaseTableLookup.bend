# proofs of laws/CaseTableLookup.bend
import Base
import ../src/str.bend as Str
import ../laws/CaseTableLookup.bend as Laws

def Laws.case_multi(ms, rules, x, s, e):
  %Equal.sym(Maybe<&2, String>, Str.text.case.multi(ms, x), Some{s}, e)
    : {Str.text.case.one(_, x, rules) == s : String}
  {==}

def Laws.case_rules(ms, rules, x, e):
  %Equal.sym(Maybe<&2, String>, Str.text.case.multi(ms, x), None{}, e)
    : {Str.text.case.one(_, x, rules)
      == SCon{Chr{Str.text.case.apply(rules, x)}, SNil{}} : String}
  {==}

def Laws.multi_none(_x):
  {==}

def Laws.multi_hit(from, to, rest, x, e):
  %Equal.sym(Bool, U32.is_eq(from, x), True{}, e)
    : {Str.text.case.found(_, to, _u => Str.text.case.multi(rest, x))
      == Some{to} : Maybe<&2, String>}
  {==}

def Laws.multi_miss(from, to, rest, x, e):
  %Equal.sym(Bool, U32.is_eq(from, x), False{}, e)
    : {Str.text.case.found(_, to, _u => Str.text.case.multi(rest, x))
      == Str.text.case.multi(rest, x) : Maybe<&2, String>}
  {==}

def Laws.apply_none(_x):
  {==}

def Laws.apply_hit(r, rest, x, e):
  %Equal.sym(Bool, Str.text.case.covers(r, x), True{}, e)
    : {Str.text.case.pick(_, r, x, _u => Str.text.case.apply(rest, x))
      == Str.text.case.target(r, x) : U32}
  {==}

def Laws.apply_miss(r, rest, x, e):
  %Equal.sym(Bool, Str.text.case.covers(r, x), False{}, e)
    : {Str.text.case.pick(_, r, x, _u => Str.text.case.apply(rest, x))
      == Str.text.case.apply(rest, x) : U32}
  {==}

def Laws.covers_def(_lo, _hi, _step, _to, _x):
  {==}

def Laws.target_def(_lo, _hi, _step, _to, _x):
  {==}
