# facts on appending and comparing texts, and the template scan past
# delimiters
import Base
import ../../src/text.bend as Text
import ./BoolFacts.bend as M1

# not of a true is false
law not_true:
  for a: Bool
  for e: {Bool.not(a) == True{} : Bool}
  {a == False{} : Bool}

def not_true(a, e):
  match a:
    case False{}:
      {==}
    case True{}:
      M1.gone(&1, {True{} == False{} : Bool},
        M1.clash(Equal.sym(Bool, False{}, True{}, e)))

# a true all has a true first test
law all_true_l:
  for here: Bool
  for rest: Unit -> Bool
  for e: {Text.text.all(here, rest) == True{} : Bool}
  {here == True{} : Bool}

def all_true_l(here, _rest, e):
  match here:
    case False{}:
      M1.gone(&1, {False{} == True{} : Bool},
        M1.clash(Equal.sym(Bool, False{}, True{}, e)))
    case True{}:
      {==}

# a true all has a true rest
law all_true_r:
  for here: Bool
  for rest: Unit -> Bool
  for e: {Text.text.all(here, rest) == True{} : Bool}
  {rest(Unit{}) == True{} : Bool}

def all_true_r(here, rest, e):
  match here:
    case False{}:
      M1.gone(&1, {rest(Unit{}) == True{} : Bool},
        M1.clash(Equal.sym(Bool, False{}, True{}, e)))
    case True{}:
      e

# --- Char and String facts ---

def eq.bool_cmp_self(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def eq.word_cmp_self(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          Equal.trans(Cmp, Word.cmp.fin(b, b, Word.cmp(p, t, t)),
            Word.cmp.fin(b, b, EQ{}), EQ{},
            Equal.cong(Cmp, Cmp, c => Word.cmp.fin(b, b, c),
              Word.cmp(p, t, t), EQ{}, eq.word_cmp_self(p, t)),
            eq.bool_cmp_self(b))

def eq.u32_cmp_self(u: U32) -> {U32.cmp(u, u) == EQ{} : Cmp}:
  match u:
    case U32{+w}:
      eq.word_cmp_self(32n, w)

def eq.char_eq_self(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{+x}:
      Equal.cong(Cmp, Bool, r => Cmp.is_eq(r), U32.cmp(x, x), EQ{},
        eq.u32_cmp_self(x))

# a text starts with itself, whatever follows it
law starts_self:
  for +s: String
  for +x: String
  {String.starts_with(s ++ x, s) == True{} : Bool}

def starts_self(s, x):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, c), True{}, eq.char_eq_self(c))
        : {String.starts_with.go.if(t, t ++ x, _) == True{} : Bool}
      starts_self(t, x)

# appending nothing changes nothing
law app_nil:
  for +a: String
  {a ++ "" == a : String}

def app_nil(a):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, x => SCon{h, x}, t ++ "", t, app_nil(t))

# appending is associative
law app_assoc:
  for +a: String
  for +b: String
  for +c: String
  {(a ++ b) ++ c == a ++ (b ++ c) : String}

def app_assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, x => SCon{h, x}, (t ++ b) ++ c, t ++ (b ++ c),
        app_assoc(t, b, c))

# the rest of an open delimiter is passed over into a key
law go_opening:
  for +ot: String
  for +x: String
  for +open: String
  for +close: String
  for +pairs: Text.text.Pairs()
  {Text.text.go(ot ++ x, Text.text.enter(String.length(ot)), open, close, pairs)
    == Text.text.go(x, Text.InKey{""}, open, close, pairs) : String}

def go_opening(ot, x, open, close, pairs):
  match ot:
    case SNil{}:
      {==}
    case SCon{_c, +t}:
      go_opening(t, x, open, close, pairs)

# the rest of a close delimiter is passed over into plain text
law go_closing:
  for +ct: String
  for +x: String
  for +open: String
  for +close: String
  for +pairs: Text.text.Pairs()
  {Text.text.go(ct ++ x, Text.text.leave(String.length(ct)), open, close, pairs)
    == Text.text.go(x, Text.Plain{}, open, close, pairs) : String}

def go_closing(ct, x, open, close, pairs):
  match ct:
    case SNil{}:
      {==}
    case SCon{_c, +t}:
      go_closing(t, x, open, close, pairs)

# a key with no close delimiter in it scans to the close that follows it,
# which writes the marker's replacement and goes on in plain text
law go_key:
  for +key: String
  for +acc: String
  for +rest: String
  for +open: String
  for +ch: Char
  for +ct: String
  for +pairs: Text.text.Pairs()
  for +free: {Text.text.free(SCon{ch, ct}, key, SCon{ch, ct} ++ rest) == True{}
    : Bool}
  {Text.text.go(key ++ (SCon{ch, ct} ++ rest), Text.InKey{acc}, open,
    SCon{ch, ct}, pairs)
    == Text.text.put(open, SCon{ch, ct}, acc ++ key,
      Text.text.value(pairs, acc ++ key))
    ++ Text.text.go(rest, Text.Plain{}, open, SCon{ch, ct}, pairs) : String}

def go_key(key, acc, rest, open, ch, ct, pairs, free):
  match key:
    case SNil{}:
      %Equal.sym(Bool, String.starts_with(SCon{ch, ct} ++ rest, SCon{ch, ct}),
        True{}, starts_self(SCon{ch, ct}, rest))
        : {Text.text.join(Text.text.shut(_, ch, acc, open, SCon{ch, ct}, pairs),
          next => Text.text.go(ct ++ rest, next, open, SCon{ch, ct}, pairs))
          == Text.text.put(open, SCon{ch, ct}, acc ++ "",
            Text.text.value(pairs, acc ++ ""))
          ++ Text.text.go(rest, Text.Plain{}, open, SCon{ch, ct}, pairs)
          : String}
      %go_closing(ct, rest, open, SCon{ch, ct}, pairs)
        : {Text.text.put(open, SCon{ch, ct}, acc, Text.text.value(pairs, acc))
          ++ Text.text.go(ct ++ rest, Text.text.leave(String.length(ct)), open,
            SCon{ch, ct}, pairs)
          == Text.text.put(open, SCon{ch, ct}, acc ++ "",
            Text.text.value(pairs, acc ++ "")) ++ _ : String}
      Equal.cong(String, String,
        +x => Text.text.put(open, SCon{ch, ct}, x, Text.text.value(pairs, x))
          ++ Text.text.go(ct ++ rest, Text.text.leave(String.length(ct)), open,
            SCon{ch, ct}, pairs),
        acc, acc ++ "", Equal.sym(String, acc ++ "", acc, app_nil(acc)))
    case SCon{+h, +k}:
      %Equal.sym(Bool,
        String.starts_with(SCon{h, k ++ (SCon{ch, ct} ++ rest)}, SCon{ch, ct}),
        False{},
        not_true(
          String.starts_with(SCon{h, k ++ (SCon{ch, ct} ++ rest)}, SCon{ch, ct}),
          all_true_l(Bool.not(String.starts_with(
            SCon{h, k ++ (SCon{ch, ct} ++ rest)}, SCon{ch, ct})),
            _u => Text.text.free(SCon{ch, ct}, k, SCon{ch, ct} ++ rest), free)))
        : {Text.text.join(Text.text.shut(_, h, acc, open, SCon{ch, ct}, pairs),
          next => Text.text.go(k ++ (SCon{ch, ct} ++ rest), next, open,
            SCon{ch, ct}, pairs))
          == Text.text.put(open, SCon{ch, ct}, acc ++ SCon{h, k},
            Text.text.value(pairs, acc ++ SCon{h, k}))
          ++ Text.text.go(rest, Text.Plain{}, open, SCon{ch, ct}, pairs)
          : String}
      Equal.trans(String,
        Text.text.go(k ++ (SCon{ch, ct} ++ rest), Text.InKey{acc ++ SCon{h, SNil{}}}, open,
          SCon{ch, ct}, pairs),
        Text.text.put(open, SCon{ch, ct}, (acc ++ SCon{h, SNil{}}) ++ k,
          Text.text.value(pairs, (acc ++ SCon{h, SNil{}}) ++ k))
          ++ Text.text.go(rest, Text.Plain{}, open, SCon{ch, ct}, pairs),
        Text.text.put(open, SCon{ch, ct}, acc ++ SCon{h, k},
          Text.text.value(pairs, acc ++ SCon{h, k}))
          ++ Text.text.go(rest, Text.Plain{}, open, SCon{ch, ct}, pairs),
        go_key(k, acc ++ SCon{h, SNil{}}, rest, open, ch, ct, pairs,
          all_true_r(Bool.not(String.starts_with(
            SCon{h, k ++ (SCon{ch, ct} ++ rest)}, SCon{ch, ct})),
            _u => Text.text.free(SCon{ch, ct}, k, SCon{ch, ct} ++ rest), free)),
        Equal.cong(String, String,
          +x => Text.text.put(open, SCon{ch, ct}, x, Text.text.value(pairs, x))
            ++ Text.text.go(rest, Text.Plain{}, open, SCon{ch, ct}, pairs),
          (acc ++ SCon{h, SNil{}}) ++ k, acc ++ SCon{h, k}, app_assoc(acc, SCon{h, SNil{}}, k)))

# a marker at the start of a template: the open delimiter is found, passed
# over, and the key scanned
law go_marker:
  for +oh: Char
  for +ot: String
  for +x: String
  for +close: String
  for +pairs: Text.text.Pairs()
  {Text.text.go(SCon{oh, ot} ++ x, Text.Plain{}, SCon{oh, ot}, close, pairs)
    == Text.text.go(x, Text.InKey{""}, SCon{oh, ot}, close, pairs) : String}

def go_marker(oh, ot, x, close, pairs):
  %Equal.sym(Bool, String.starts_with(SCon{oh, ot} ++ x, SCon{oh, ot}), True{},
    starts_self(SCon{oh, ot}, x))
    : {Text.text.join(Text.text.plain(_, oh, SCon{oh, ot}),
      next => Text.text.go(ot ++ x, next, SCon{oh, ot}, close, pairs))
      == Text.text.go(x, Text.InKey{""}, SCon{oh, ot}, close, pairs) : String}
  go_opening(ot, x, SCon{oh, ot}, close, pairs)
