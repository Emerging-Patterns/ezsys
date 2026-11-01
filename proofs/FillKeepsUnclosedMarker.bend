# proofs of laws/FillKeepsUnclosedMarker.bend
import Base
import ../src/text.bend as Text
import ../laws/FillKeepsUnclosedMarker.bend as Laws
import ./lemmas/BoolFacts.bend as M1
import ./lemmas/TextScan.bend as M2

# a key with no close delimiter in it, at the end of the template, is
# written back with its open delimiter
law go_unclosed:
  for +key: String
  for +acc: String
  for +open: String
  for +close: String
  for +pairs: Text.text.Pairs()
  for +e: {Text.text.marked(close, key) == False{} : Bool}
  {Text.text.go(key, Text.InKey{acc}, open, close, pairs)
    == open ++ (acc ++ key) : String}

def go_unclosed(key, acc, open, close, pairs, e):
  match key:
    case SNil{}:
      Equal.cong(String, String, x => open ++ x, acc, acc ++ "",
        Equal.sym(String, acc ++ "", acc, M2.app_nil(acc)))
    case SCon{+h, +k}:
      %Equal.sym(Bool, String.starts_with(SCon{h, k}, close), False{},
        M1.any_false_l(String.starts_with(SCon{h, k}, close),
          _u => Text.text.marked(close, k), e))
        : {Text.text.join(Text.text.shut(_, h, acc, open, close, pairs),
          next => Text.text.go(k, next, open, close, pairs))
          == open ++ (acc ++ SCon{h, k}) : String}
      Equal.trans(String,
        Text.text.go(k, Text.InKey{acc ++ SCon{h, SNil{}}}, open, close, pairs),
        open ++ ((acc ++ SCon{h, SNil{}}) ++ k),
        open ++ (acc ++ SCon{h, k}),
        go_unclosed(k, acc ++ SCon{h, SNil{}}, open, close, pairs,
          M1.any_false_r(String.starts_with(SCon{h, k}, close),
            _u => Text.text.marked(close, k), e)),
        Equal.cong(String, String, x => open ++ x,
          (acc ++ SCon{h, SNil{}}) ++ k, acc ++ SCon{h, k},
          M2.app_assoc(acc, SCon{h, SNil{}}, k)))

def Laws.fill_unclosed(oh, ot, ch, ct, key, pairs, e):
  Equal.trans(String,
    Text.text.go(SCon{oh, ot} ++ key, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct},
      pairs),
    Text.text.go(key, Text.InKey{""}, SCon{oh, ot}, SCon{ch, ct}, pairs),
    SCon{oh, ot} ++ key,
    M2.go_marker(oh, ot, key, SCon{ch, ct}, pairs),
    go_unclosed(key, "", SCon{oh, ot}, SCon{ch, ct}, pairs, e))
