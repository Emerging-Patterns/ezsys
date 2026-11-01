# proofs of laws/TruncateTakesPrefix.bend
import Base
import ../src/str.bend as Str
import ../laws/TruncateTakesPrefix.bend as Laws

def Laws.trunc_split(s, n):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      match n:
        case 0n:
          {==}
        case 1n+k:
          Equal.cong(String, String, y => SCon{h, y},
            Str.text.truncate(t, k) ++ String.drop(t, k), t,
            Laws.trunc_split(t, k))

def Laws.trunc_length(s, n):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      match n:
        case 0n:
          {==}
        case 1n+k:
          Equal.cong(Nat, Nat, m => 1n+m,
            String.length(Str.text.truncate(t, k)),
            Nat.min(String.length(t), k), Laws.trunc_length(t, k))
