# proofs of laws/FindAgreesWithContains.bend
import Base
import ../src/str.bend as Str
import ../laws/FindAgreesWithContains.bend as Laws

# a place one further on is a place exactly when the first is
law inc_some:
  for m: Maybe<&2, U32>
  {Maybe.is_some(&2, U32, Str.text.find.inc(m)) == Maybe.is_some(&2, U32, m)
    : Bool}

def inc_some(m):
  match m:
    case None{}:
      {==}
    case Some{_i}:
      {==}

# one step of find answers a place exactly when one step of contains holds
law find_at_some:
  for b: Bool
  for +t: String
  for +needle: String
  for ih: {Maybe.is_some(&2, U32, Str.text.find(t, needle))
    == String.contains(t, needle) : Bool}
  {Maybe.is_some(&2, U32, Str.text.find.at(b, _u => Str.text.find(t, needle)))
    == String.contains.if(t, needle, b) : Bool}

def find_at_some(b, t, needle, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool,
        Maybe.is_some(&2, U32, Str.text.find.inc(Str.text.find(t, needle))),
        Maybe.is_some(&2, U32, Str.text.find(t, needle)),
        String.contains(t, needle),
        inc_some(Str.text.find(t, needle)), ih)

def Laws.find_contains(s, needle):
  match s:
    case SNil{}:
      match needle:
        case SNil{}:
          {==}
        case SCon{_h, _t}:
          {==}
    case SCon{+h, +t}:
      find_at_some(String.starts_with(SCon{h, t}, needle), t, needle,
        Laws.find_contains(t, needle))
