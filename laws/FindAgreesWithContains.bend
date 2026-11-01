# For every text and needle, `text.find` answers a place exactly when Base's
# `String.contains` holds.
import Base
import ../src/str.bend as Str

# LAW: find answers a place exactly when Base's String.contains holds
law find_contains:
  for +s: String
  for +needle: String
  {Maybe.is_some(&2, U32, Str.text.find(s, needle))
    == String.contains(s, needle) : Bool}
