# ezsys/src/text: text templates. A marker is an open delimiter, a key and a
# close delimiter, `{{name}}` for `text.fill`. The scan reads the template
# once, left to right, one character a step: at an open delimiter it starts a
# key, and the key runs to the first close delimiter after it. A known key is
# replaced by its value, written as it is (a value is never scanned again);
# an unknown key, or a marker with no close, is left as written. Markers do
# not nest. An empty open or close delimiter marks nothing.
import Base

# where the scan is: in plain text, passing over the rest of an open
# delimiter, inside a key, or passing over the rest of a close delimiter
type Mode is Data:
  Plain{}
  Opening{left: Nat}
  InKey{key: String}
  Closing{left: Nat}

# the keys and values, reusable
def text.Pairs() -> Data:
  List<&2, Sigma<&2, &2, String, _ => String>>

# a caller's pairs as reusable ones, in their order
def text.own(xs: List<(String & String)>) -> text.Pairs():
  match xs:
    case Nil{}:
      Nil{}
    case Con{(+key, +value), rest}:
      Con{(key, value), text.own(rest)}

# this pair's value when its key is the one asked for, else the rest's
def text.value.pick(
  hit: Bool,
  value: String,
  rest: Unit -> Maybe<&2, String>
) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{value}
    case False{}:
      rest(Unit{})

# the value a key names: the first pair with that key
def text.value(pairs: text.Pairs(), +key: String) -> Maybe<&2, String>:
  match pairs:
    case Nil{}:
      None{}
    case Con{(name, value), rest}:
      text.value.pick(String.eq(name, key), value,
        _u => text.value(rest, key))

# the characters of a delimiter after its first
def text.tail(delim: String) -> Nat:
  match delim:
    case SNil{}:
      0n
    case SCon{_hd, tl}:
      String.length(tl)

# the mode after an open delimiter's first character, with `left` to pass
def text.enter(left: Nat) -> Mode:
  match left:
    case 0n:
      InKey{""}
    case 1n+more:
      Opening{more}

# the mode after a close delimiter's first character, with `left` to pass
def text.leave(left: Nat) -> Mode:
  match left:
    case 0n:
      Plain{}
    case 1n+more:
      Closing{more}

# what a finished marker becomes: its value, or the marker as written
def text.put(
  +open: String,
  +close: String,
  key: String,
  got: Maybe<&2, String>
) -> String:
  match got:
    case None{}:
      open ++ (key ++ close)
    case Some{value}:
      value

# a character in plain text: the start of a marker, or itself
def text.plain(at: Bool, hd: Char, +open: String) -> String & Mode:
  match at:
    case False{}:
      (SCon{hd, SNil{}}, Plain{})
    case True{}:
      ("", text.enter(text.tail(open)))

# a character in a key: the start of the close delimiter, or part of the key
def text.shut(
  at: Bool,
  hd: Char,
  +key: String,
  +open: String,
  +close: String,
  +pairs: text.Pairs()
) -> String & Mode:
  match at:
    case False{}:
      ("", InKey{key ++ SCon{hd, SNil{}}})
    case True{}:
      (text.put(open, close, key, text.value(pairs, key)),
        text.leave(text.tail(close)))

# one character: what it writes and the mode after it
def text.step(
  +hd: Char,
  +tl: String,
  mode: Mode,
  +open: String,
  +close: String,
  +pairs: text.Pairs()
) -> String & Mode:
  match mode:
    case Plain{}:
      text.plain(String.starts_with(SCon{hd, tl}, open), hd, open)
    case Opening{left}:
      ("", text.enter(left))
    case InKey{key}:
      text.shut(String.starts_with(SCon{hd, tl}, close), hd, key, open, close,
        pairs)
    case Closing{left}:
      ("", text.leave(left))

# the end of the template: an unclosed marker is written as it was
def text.end(mode: Mode, +open: String) -> String:
  match mode:
    case Plain{}:
      ""
    case Opening{_left}:
      ""
    case InKey{key}:
      open ++ key
    case Closing{_left}:
      ""

# write a step's text, then scan on in the mode after it
def text.join(pair: String & Mode, rest: Mode -> String) -> String:
  (out, next) = pair
  out ++ rest(next)

# the scan
def text.go(
  tpl: String,
  mode: Mode,
  +open: String,
  +close: String,
  +pairs: text.Pairs()
) -> String:
  match tpl:
    case SNil{}:
      text.end(mode, open)
    case SCon{+hd, +tl}:
      text.join(text.step(hd, tl, mode, open, close, pairs),
        next => text.go(tl, next, open, close, pairs))

# true when here is true, else what the rest says
def text.any(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# false when here is false, else what the rest says
def text.all(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case False{}:
      False{}
    case True{}:
      rest(Unit{})

# whether an open delimiter starts anywhere in the text
def text.marked(+open: String, tpl: String) -> Bool:
  match tpl:
    case SNil{}:
      False{}
    case SCon{+hd, +tl}:
      text.any(String.starts_with(SCon{hd, tl}, open),
        _u => text.marked(open, tl))

# whether no close delimiter starts at any character of key, in key ++ after
def text.free(+close: String, key: String, +after: String) -> Bool:
  match key:
    case SNil{}:
      True{}
    case SCon{+hd, +tl}:
      text.all(Bool.not(String.starts_with(SCon{hd, tl ++ after}, close)),
        _u => text.free(close, tl, after))

# every marker between open and close replaced by its key's value
def text.fill_with(
  open: String,
  close: String,
  tpl: String,
  pairs: text.Pairs()
) -> String:
  match open close:
    case SNil{} _:
      tpl
    case SCon{_oh, _ot} SNil{}:
      tpl
    case SCon{oh, ot} SCon{ch, ct}:
      text.go(tpl, Plain{}, SCon{oh, ot}, SCon{ch, ct}, pairs)

# every `{{key}}` marker replaced by its key's value
def text.fill(tpl: String, pairs: text.Pairs()) -> String:
  text.fill_with("{{", "}}", tpl, pairs)
