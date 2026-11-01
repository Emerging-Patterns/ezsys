# For every key in which no `C` starts (`text.marked` of `C` is false),
# filling `O ++ key` (a marker with no close) is exactly `O ++ key`.
import Base
import ../src/text.bend as Text

# LAW: a marker with no close delimiter is left as written
law fill_unclosed:
  for +oh: Char
  for +ot: String
  for +ch: Char
  for +ct: String
  for +key: String
  for +pairs: Text.text.Pairs()
  for +e: {Text.text.marked(SCon{ch, ct}, key) == False{} : Bool}
  {Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, SCon{oh, ot} ++ key, pairs)
    == SCon{oh, ot} ++ key : String}
