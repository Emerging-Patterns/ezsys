# For every template and pairs, `text.fill` is `text.fill_with` with `{{` and
# `}}`.
import Base
import ../src/text.bend as Text

# LAW: text.fill is text.fill_with with {{ and }}
law fill_braces:
  for t: String
  for pairs: Text.text.Pairs()
  {Text.text.fill(t, pairs) == Text.text.fill_with("{{", "}}", t, pairs)
    : String}
