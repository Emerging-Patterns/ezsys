# proofs of laws/PadRightFillsSpaces.bend
import Base
import ../src/str.bend as Str
import ../laws/PadRightFillsSpaces.bend as Laws
import ./lemmas/TextScan.bend as M1

# --- width ---

def Laws.pad_form(s, n):
  match s:
    case SNil{}:
      match n:
        case 0n:
          {==}
        case 1n+_k:
          {==}
    case SCon{+h, +t}:
      match n:
        case 0n:
          Equal.sym(String, SCon{h, t} ++ "", SCon{h, t}, M1.app_nil(SCon{h, t}))
        case 1n+k:
          Equal.cong(String, String, y => SCon{h, y}, Str.text.pad_right(t, k),
            t ++ String.repeat(" ", Nat.sub(k, String.length(t))),
            Laws.pad_form(t, k))

# n spaces are n code points
law repeat_len:
  for n: Nat
  {String.length(String.repeat(" ", n)) == n : Nat}

def repeat_len(n):
  match n:
    case 0n:
      {==}
    case 1n+k:
      Equal.cong(Nat, Nat, m => 1n+m, String.length(String.repeat(" ", k)), k,
        repeat_len(k))

def Laws.pad_length(s, n):
  match s:
    case SNil{}:
      repeat_len(n)
    case SCon{+h, +t}:
      match n:
        case 0n:
          {==}
        case 1n+k:
          Equal.cong(Nat, Nat, m => 1n+m,
            String.length(Str.text.pad_right(t, k)),
            Nat.max(String.length(t), k), Laws.pad_length(t, k))
