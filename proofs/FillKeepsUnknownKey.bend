# proofs of laws/FillKeepsUnknownKey.bend
import Base
import ../src/text.bend as Text
import ../laws/FillKeepsUnknownKey.bend as Laws
import ./lemmas/TextScan.bend as M1

def Laws.fill_unknown(oh, ot, ch, ct, key, rest, pairs, missing, free):
  Equal.trans(String,
    Text.text.go(SCon{oh, ot} ++ (key ++ (SCon{ch, ct} ++ rest)), Text.Plain{},
      SCon{oh, ot}, SCon{ch, ct}, pairs),
    Text.text.go(key ++ (SCon{ch, ct} ++ rest), Text.InKey{""}, SCon{oh, ot},
      SCon{ch, ct}, pairs),
    (SCon{oh, ot} ++ (key ++ SCon{ch, ct}))
      ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct}, pairs),
    M1.go_marker(oh, ot, key ++ (SCon{ch, ct} ++ rest), SCon{ch, ct}, pairs),
    Equal.trans(String,
      Text.text.go(key ++ (SCon{ch, ct} ++ rest), Text.InKey{""}, SCon{oh, ot},
        SCon{ch, ct}, pairs),
      Text.text.put(SCon{oh, ot}, SCon{ch, ct}, key,
        Text.text.value(pairs, key))
        ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct}, pairs),
      (SCon{oh, ot} ++ (key ++ SCon{ch, ct}))
        ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct}, pairs),
      M1.go_key(key, "", rest, SCon{oh, ot}, ch, ct, pairs, free),
      Equal.cong(Maybe<&2, String>, String,
        m => Text.text.put(SCon{oh, ot}, SCon{ch, ct}, key, m)
          ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct},
            pairs),
        Text.text.value(pairs, key), None{}, missing)))
