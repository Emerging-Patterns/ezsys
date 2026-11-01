# For every key no pair has, in which no `C` starts before the close delimiter
# that follows it, and every text `rest`, filling `O ++ key ++ C ++ rest` is
# exactly `O ++ key ++ C` followed by filling `rest`.
import Base
import ../src/text.bend as Text

# LAW: a marker whose key has no value is left as written
law fill_unknown:
  for +oh: Char
  for +ot: String
  for +ch: Char
  for +ct: String
  for +key: String
  for +rest: String
  for +pairs: Text.text.Pairs()
  for +missing: {Text.text.value(pairs, key) == None{} : Maybe<&2, String>}
  for +free: {Text.text.free(SCon{ch, ct}, key, SCon{ch, ct} ++ rest) == True{}
    : Bool}
  {Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct},
    SCon{oh, ot} ++ (key ++ (SCon{ch, ct} ++ rest)), pairs)
    == (SCon{oh, ot} ++ (key ++ SCon{ch, ct}))
    ++ Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, rest, pairs) : String}
