# proofs of laws/SplitKeepsEmptyPieces.bend
import Base
import ../src/str.bend as Str
import ../laws/SplitKeepsEmptyPieces.bend as Laws
import ./lemmas/TextScan.bend as M1

def Laws.split_end(_sh, _st):
  {==}

# the rest of a found separator is passed over
law split_skip:
  for +st: String
  for +x: String
  for +sep: String
  {Str.text.split.go(st ++ x, String.length(st), sep)
    == Str.text.split.go(x, 0n, sep) : List<&2, String>}

def split_skip(st, x, sep):
  match st:
    case SNil{}:
      {==}
    case SCon{_c, +t}:
      split_skip(t, x, sep)

def Laws.split_hit(sh, st, rest):
  %Equal.sym(Bool, String.starts_with(SCon{sh, st} ++ rest, SCon{sh, st}),
    True{}, M1.starts_self(SCon{sh, st}, rest))
    : {Str.text.split.at(_, sh, String.length(st),
      k => Str.text.split.go(st ++ rest, k, SCon{sh, st}))
      == SNil{} <> Str.text.split.go(rest, 0n, SCon{sh, st})
      : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>, y => SNil{} <> y,
    Str.text.split.go(st ++ rest, String.length(st), SCon{sh, st}),
    Str.text.split.go(rest, 0n, SCon{sh, st}),
    split_skip(st, rest, SCon{sh, st}))

def Laws.split_miss(h, t, sh, st, e):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, SCon{sh, st}), False{}, e)
    : {Str.text.split.at(_, h, String.length(st),
      k => Str.text.split.go(t, k, SCon{sh, st}))
      == Str.text.split.push(h, Str.text.split.go(t, 0n, SCon{sh, st}))
      : List<&2, String>}
  {==}

def Laws.split_push(_h, _p, _ps):
  {==}

# pushing a character never answers no pieces
law push_some:
  for h: Char
  for ps: List<&2, String>
  {List.is_empty(&2, String, Str.text.split.push(h, ps)) == False{} : Bool}

def push_some(_h, ps):
  match ps:
    case Nil{}:
      {==}
    case _p <> _r:
      {==}

# a step of the scan never answers no pieces
law split_at_some:
  for b: Bool
  for h: Char
  for left: Nat
  for next: Nat -> List<&2, String>
  {List.is_empty(&2, String, Str.text.split.at(b, h, left, next)) == False{}
    : Bool}

def split_at_some(b, h, _left, next):
  match b:
    case True{}:
      {==}
    case False{}:
      push_some(h, next(0n))

# the scan never answers no pieces
law split_go_some:
  for +s: String
  for +skip: Nat
  for +sep: String
  {List.is_empty(&2, String, Str.text.split.go(s, skip, sep)) == False{}
    : Bool}

def split_go_some(s, skip, sep):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      match skip:
        case 0n:
          split_at_some(String.starts_with(SCon{h, t}, sep), h,
            Str.text.after(sep), k => Str.text.split.go(t, k, sep))
        case 1n+k:
          split_go_some(t, k, sep)

def Laws.split_some(s, sh, st):
  split_go_some(s, 0n, SCon{sh, st})

def Laws.split_whole(_s):
  {==}
