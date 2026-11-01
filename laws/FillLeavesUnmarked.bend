# For every template in which no open delimiter starts (`text.marked` is
# false), and for every template when either delimiter is empty,
# `text.fill_with` answers the template unchanged.
#
# A marker is an open delimiter, a key and a close delimiter.
# `text.fill(template, pairs)` uses `{{` and `}}`, so `{{name}}` is the marker
# for the key `name`; `text.fill_with(open, close, template, pairs)` takes the
# delimiters, so the whole-line `<!--NAME-->` markers of a page shell are
# `text.fill_with("<!--", "-->", shell, pairs)`. The scan reads the template
# once, left to right: at an open delimiter a key starts, and it runs to the
# first close delimiter after it, so keys are matched exactly (spaces
# included) and markers do not nest. A key's value is the value of the first
# pair with that key, and it is written as it is, never scanned again. A key
# no pair has, and a marker with no close delimiter, are left as written. An
# empty delimiter marks nothing. The laws state these for src/text.bend's
# `text.fill_with`, which takes the pairs as a reusable list; main.bend copies
# the caller's pairs into one in order (laws/FirstPairGivesValue.bend).
import Base
import ../src/text.bend as Text

# --- text templates ---

# LAW: a template with no open delimiter in it is unchanged
law fill_unmarked:
  for open: String
  for close: String
  for t: String
  for pairs: Text.text.Pairs()
  for e: {Text.text.marked(open, t) == False{} : Bool}
  {Text.text.fill_with(open, close, t, pairs) == t : String}

# LAW: an empty open delimiter marks nothing
law fill_open_empty:
  for close: String
  for t: String
  for pairs: Text.text.Pairs()
  {Text.text.fill_with("", close, t, pairs) == t : String}

# LAW: an empty close delimiter marks nothing
law fill_close_empty:
  for open: String
  for t: String
  for pairs: Text.text.Pairs()
  {Text.text.fill_with(open, "", t, pairs) == t : String}
