# For every character `h` and text `t` such that `O` does not start at `h`,
# filling `h` followed by `t` is `h` followed by filling `t`.
import Base
import ../src/text.bend as Text

# LAW: a character where no open delimiter starts is written as it is
law fill_plain:
  for oh: Char
  for ot: String
  for ch: Char
  for ct: String
  for h: Char
  for t: String
  for pairs: Text.text.Pairs()
  for e: {String.starts_with(SCon{h, t}, SCon{oh, ot}) == False{} : Bool}
  {Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, SCon{h, t}, pairs)
    == SCon{h, Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, t, pairs)}
    : String}
