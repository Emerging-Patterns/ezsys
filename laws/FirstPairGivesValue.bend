# A key's value is the value of the first pair whose key equals it, and there
# is none when no pair has the key; the caller's pairs are kept in their
# order.
import Base
import ../src/text.bend as Text

# LAW: no pairs, no value
law value_none:
  for key: String
  {Text.text.value([], key) == None{} : Maybe<&2, String>}

# LAW: the first pair with the key gives its value
law value_hit:
  for k: String
  for v: String
  for rest: Text.text.Pairs()
  for key: String
  for e: {String.eq(k, key) == True{} : Bool}
  {Text.text.value((k, v) <> rest, key) == Some{v} : Maybe<&2, String>}

# LAW: a pair with another key is passed over
law value_miss:
  for k: String
  for v: String
  for rest: Text.text.Pairs()
  for key: String
  for e: {String.eq(k, key) == False{} : Bool}
  {Text.text.value((k, v) <> rest, key) == Text.text.value(rest, key)
    : Maybe<&2, String>}

# LAW: the caller's pairs are kept in their order
law own_order:
  for k: String
  for v: String
  for rest: List<(String & String)>
  {Text.text.own((k, v) <> rest) == (k, v) <> Text.text.own(rest)
    : Text.text.Pairs()}
