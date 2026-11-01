# proofs of laws/FillLeavesUnmarked.bend
import Base
import ../src/text.bend as Text
import ../laws/FillLeavesUnmarked.bend as Laws
import ./lemmas/BoolFacts.bend as M1

# --- text templates ---

def Laws.fill_open_empty(_close, _t, _pairs):
  {==}

def Laws.fill_close_empty(open, _t, _pairs):
  match open:
    case SNil{}:
      {==}
    case SCon{_h, _r}:
      {==}

# plain text with no open delimiter in it scans to itself
law go_plain:
  for +t: String
  for +open: String
  for +close: String
  for +pairs: Text.text.Pairs()
  for +e: {Text.text.marked(open, t) == False{} : Bool}
  {Text.text.go(t, Text.Plain{}, open, close, pairs) == t : String}

def go_plain(t, open, close, pairs, e):
  match t:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      %Equal.sym(Bool, String.starts_with(SCon{h, r}, open), False{},
        M1.any_false_l(String.starts_with(SCon{h, r}, open),
          _u => Text.text.marked(open, r), e))
        : {Text.text.join(Text.text.plain(_, h, open),
          next => Text.text.go(r, next, open, close, pairs)) == SCon{h, r}
          : String}
      Equal.cong(String, String, x => SCon{h, x},
        Text.text.go(r, Text.Plain{}, open, close, pairs), r,
        go_plain(r, open, close, pairs,
          M1.any_false_r(String.starts_with(SCon{h, r}, open),
            _u => Text.text.marked(open, r), e)))

def Laws.fill_unmarked(open, close, t, pairs, e):
  match open:
    case SNil{}:
      {==}
    case SCon{oh, ot}:
      match close:
        case SNil{}:
          {==}
        case SCon{ch, ct}:
          go_plain(t, SCon{oh, ot}, SCon{ch, ct}, pairs, e)
