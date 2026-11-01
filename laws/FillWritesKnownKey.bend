# For every key with a value `v`, in which no `C` starts before the close
# delimiter that follows it (`text.free`), and every text `rest`, filling `O
# ++ key ++ C ++ rest` is exactly `v` followed by filling `rest`.
import Base
import ../src/text.bend as Text

# LAW: a marker whose key has a value is replaced by exactly that value
law fill_known:
  for +oh: Char
  for +ot: String
  for +ch: Char
  for +ct: String
  for +key: String
  for +value: String
  for +rest: String
  for +pairs: Text.text.Pairs()
  for +found: {Text.text.value(pairs, key) == Some{value} : Maybe<&2, String>}
  for +free: {Text.text.free(SCon{ch, ct}, key, SCon{ch, ct} ++ rest) == True{}
    : Bool}
  {Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct},
    SCon{oh, ot} ++ (key ++ (SCon{ch, ct} ++ rest)), pairs)
    == value ++ Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, rest, pairs)
    : String}
