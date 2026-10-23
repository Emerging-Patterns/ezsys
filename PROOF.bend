# ezsys: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./src/step.bend as Step
import ./src/clock.bend as Clock
import ./src/text.bend as Text
import ./LAWS.bend as Laws

# --- Bool facts ---

# Unit for True, Empty for False: tells them apart
def bit(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

# True is never False
def clash(e: {True{} == False{} : Bool}) -> Empty:
  %e : bit(_)
  Unit{}

# anything follows from Empty
def gone(a, -A: Kind(a), e: Empty) -> A:
  match e:

# a false any has a false first test
law any_false_l:
  for here: Bool
  for rest: Unit -> Bool
  for e: {Text.text.any(here, rest) == False{} : Bool}
  {here == False{} : Bool}

def any_false_l(here, _rest, e):
  match here:
    case False{}:
      {==}
    case True{}:
      gone(&1, {True{} == False{} : Bool}, clash(e))

# a false any has a false rest
law any_false_r:
  for here: Bool
  for rest: Unit -> Bool
  for e: {Text.text.any(here, rest) == False{} : Bool}
  {rest(Unit{}) == False{} : Bool}

def any_false_r(here, rest, e):
  match here:
    case False{}:
      e
    case True{}:
      gone(&1, {rest(Unit{}) == False{} : Bool}, clash(e))

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
      gone(&1, {True{} == False{} : Bool},
        clash(Equal.sym(Bool, False{}, True{}, e)))

# a true all has a true first test
law all_true_l:
  for here: Bool
  for rest: Unit -> Bool
  for e: {Text.text.all(here, rest) == True{} : Bool}
  {here == True{} : Bool}

def all_true_l(here, _rest, e):
  match here:
    case False{}:
      gone(&1, {False{} == True{} : Bool},
        clash(Equal.sym(Bool, False{}, True{}, e)))
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
      gone(&1, {rest(Unit{}) == True{} : Bool},
        clash(Equal.sym(Bool, False{}, True{}, e)))
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

# --- files and environment ---

def Laws.read_fail(_code, _why, _got):
  {==}

def Laws.read_end(_got):
  {==}

def Laws.read_more(_h, _t, _got):
  {==}

def Laws.save_tmp(_path):
  {==}

def Laws.save_fail(_code, _why):
  {==}

def Laws.save_move(_u):
  {==}

def Laws.env_set(_value, _fallback):
  {==}

def Laws.env_unset(_code, _why, _fallback):
  {==}

# --- wall clock ---

def Laws.iso_width(_secs, _ms):
  {==}

def Laws.iso_split(_secs, _ms):
  {==}

def Laws.clock_fields(_sod, _ms):
  {==}

def Laws.date_fields(_days):
  {==}

def Laws.last_second(_ms):
  {==}

# --- text templates ---

def Laws.fill_open_empty(_close, _t, _pairs):
  {==}

def Laws.fill_close_empty(open, _t, _pairs):
  match open:
    case SNil{}:
      {==}
    case SCon{_h, _r}:
      {==}

def Laws.value_none(_key):
  {==}

def Laws.own_order(_k, _v, _rest):
  {==}

def Laws.fill_braces(_t, _pairs):
  {==}

# --- anchor days: the day number rewritten to its literal ---

def Laws.leap_2000(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 11016, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2000-02-29T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.leap_2000_after(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 11017, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2000-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.leap_2024(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 19782, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2024-02-29T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.leap_2024_after(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 19783, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2024-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.common_2023(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 19416, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2023-02-28T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.common_2023_after(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 19417, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2023-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.century_2100(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 47540, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2100-02-28T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.century_2100_after(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 47541, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2100-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.epoch(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 0, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "1970-01-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.eve_2000(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 10956, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "1999-12-31T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.day_2000(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 10957, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2000-01-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.last_day(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 49710, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2106-02-07T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.value_hit(k, v, rest, key, e):
  %Equal.sym(Bool, String.eq(k, key), True{}, e)
    : {Text.text.value.pick(_, v, _u => Text.text.value(rest, key)) == Some{v}
      : Maybe<&2, String>}
  {==}

def Laws.value_miss(k, v, rest, key, e):
  %Equal.sym(Bool, String.eq(k, key), False{}, e)
    : {Text.text.value.pick(_, v, _u => Text.text.value(rest, key))
      == Text.text.value(rest, key) : Maybe<&2, String>}
  {==}

# --- the scan ---

def Laws.fill_plain(oh, ot, ch, ct, h, t, pairs, e):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, SCon{oh, ot}), False{}, e)
    : {Text.text.join(Text.text.plain(_, h, SCon{oh, ot}),
      next => Text.text.go(t, next, SCon{oh, ot}, SCon{ch, ct}, pairs))
      == SCon{h, Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, t, pairs)}
      : String}
  {==}

# plain text with no open delimiter in it scans to itself
law go_plain:
  for +t: String
  for +open: String
  for +close: String
  for +pairs: Text.text.Pairs()
  for +e: {Text.text.marked(open, t) == False{} : Bool}
  {Text.text.go(t, Text.Plain{}, open, close, pairs) == t : String}

def go_plain(t, open, close, pairs, e):
  match t:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      %Equal.sym(Bool, String.starts_with(SCon{h, r}, open), False{},
        any_false_l(String.starts_with(SCon{h, r}, open),
          _u => Text.text.marked(open, r), e))
        : {Text.text.join(Text.text.plain(_, h, open),
          next => Text.text.go(r, next, open, close, pairs)) == SCon{h, r}
          : String}
      Equal.cong(String, String, x => SCon{h, x},
        Text.text.go(r, Text.Plain{}, open, close, pairs), r,
        go_plain(r, open, close, pairs,
          any_false_r(String.starts_with(SCon{h, r}, open),
            _u => Text.text.marked(open, r), e)))

def Laws.fill_unmarked(open, close, t, pairs, e):
  match open:
    case SNil{}:
      {==}
    case SCon{oh, ot}:
      match close:
        case SNil{}:
          {==}
        case SCon{ch, ct}:
          go_plain(t, SCon{oh, ot}, SCon{ch, ct}, pairs, e)

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

# a key with no close delimiter in it, at the end of the template, is
# written back with its open delimiter
law go_unclosed:
  for +key: String
  for +acc: String
  for +open: String
  for +close: String
  for +pairs: Text.text.Pairs()
  for +e: {Text.text.marked(close, key) == False{} : Bool}
  {Text.text.go(key, Text.InKey{acc}, open, close, pairs)
    == open ++ (acc ++ key) : String}

def go_unclosed(key, acc, open, close, pairs, e):
  match key:
    case SNil{}:
      Equal.cong(String, String, x => open ++ x, acc, acc ++ "",
        Equal.sym(String, acc ++ "", acc, app_nil(acc)))
    case SCon{+h, +k}:
      %Equal.sym(Bool, String.starts_with(SCon{h, k}, close), False{},
        any_false_l(String.starts_with(SCon{h, k}, close),
          _u => Text.text.marked(close, k), e))
        : {Text.text.join(Text.text.shut(_, h, acc, open, close, pairs),
          next => Text.text.go(k, next, open, close, pairs))
          == open ++ (acc ++ SCon{h, k}) : String}
      Equal.trans(String,
        Text.text.go(k, Text.InKey{acc ++ SCon{h, SNil{}}}, open, close, pairs),
        open ++ ((acc ++ SCon{h, SNil{}}) ++ k),
        open ++ (acc ++ SCon{h, k}),
        go_unclosed(k, acc ++ SCon{h, SNil{}}, open, close, pairs,
          any_false_r(String.starts_with(SCon{h, k}, close),
            _u => Text.text.marked(close, k), e)),
        Equal.cong(String, String, x => open ++ x,
          (acc ++ SCon{h, SNil{}}) ++ k, acc ++ SCon{h, k},
          app_assoc(acc, SCon{h, SNil{}}, k)))

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

def Laws.fill_known(oh, ot, ch, ct, key, value, rest, pairs, found, free):
  Equal.trans(String,
    Text.text.go(SCon{oh, ot} ++ (key ++ (SCon{ch, ct} ++ rest)), Text.Plain{},
      SCon{oh, ot}, SCon{ch, ct}, pairs),
    Text.text.go(key ++ (SCon{ch, ct} ++ rest), Text.InKey{""}, SCon{oh, ot},
      SCon{ch, ct}, pairs),
    value ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct},
      pairs),
    go_marker(oh, ot, key ++ (SCon{ch, ct} ++ rest), SCon{ch, ct}, pairs),
    Equal.trans(String,
      Text.text.go(key ++ (SCon{ch, ct} ++ rest), Text.InKey{""}, SCon{oh, ot},
        SCon{ch, ct}, pairs),
      Text.text.put(SCon{oh, ot}, SCon{ch, ct}, key,
        Text.text.value(pairs, key))
        ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct}, pairs),
      value ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct},
        pairs),
      go_key(key, "", rest, SCon{oh, ot}, ch, ct, pairs, free),
      Equal.cong(Maybe<&2, String>, String,
        m => Text.text.put(SCon{oh, ot}, SCon{ch, ct}, key, m)
          ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct},
            pairs),
        Text.text.value(pairs, key), Some{value}, found)))

def Laws.fill_unknown(oh, ot, ch, ct, key, rest, pairs, missing, free):
  Equal.trans(String,
    Text.text.go(SCon{oh, ot} ++ (key ++ (SCon{ch, ct} ++ rest)), Text.Plain{},
      SCon{oh, ot}, SCon{ch, ct}, pairs),
    Text.text.go(key ++ (SCon{ch, ct} ++ rest), Text.InKey{""}, SCon{oh, ot},
      SCon{ch, ct}, pairs),
    (SCon{oh, ot} ++ (key ++ SCon{ch, ct}))
      ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct}, pairs),
    go_marker(oh, ot, key ++ (SCon{ch, ct} ++ rest), SCon{ch, ct}, pairs),
    Equal.trans(String,
      Text.text.go(key ++ (SCon{ch, ct} ++ rest), Text.InKey{""}, SCon{oh, ot},
        SCon{ch, ct}, pairs),
      Text.text.put(SCon{oh, ot}, SCon{ch, ct}, key,
        Text.text.value(pairs, key))
        ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct}, pairs),
      (SCon{oh, ot} ++ (key ++ SCon{ch, ct}))
        ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct}, pairs),
      go_key(key, "", rest, SCon{oh, ot}, ch, ct, pairs, free),
      Equal.cong(Maybe<&2, String>, String,
        m => Text.text.put(SCon{oh, ot}, SCon{ch, ct}, key, m)
          ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct},
            pairs),
        Text.text.value(pairs, key), None{}, missing)))

def Laws.fill_unclosed(oh, ot, ch, ct, key, pairs, e):
  Equal.trans(String,
    Text.text.go(SCon{oh, ot} ++ key, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct},
      pairs),
    Text.text.go(key, Text.InKey{""}, SCon{oh, ot}, SCon{ch, ct}, pairs),
    SCon{oh, ot} ++ key,
    go_marker(oh, ot, key, SCon{ch, ct}, pairs),
    go_unclosed(key, "", SCon{oh, ot}, SCon{ch, ct}, pairs, e))

# --- the form of time.iso ---

# every digit character is shaped '#'
law digit_at_shape:
  for k: Nat
  {Laws.shape.char(Clock.time.digit.at(k)) == '#' : Char}

def digit_at_shape(k):
  match k:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+_k9:
                                      {==}

# every digit time.iso writes is shaped '#'
law digit_shape:
  for n: U32
  {Laws.shape.char(Clock.time.digit(n)) == '#' : Char}

def digit_shape(n):
  digit_at_shape(U32.to_nat((n % 10 : U32)))

# shaping a joined text is joining the shaped parts
law shape_app:
  for +a: String
  for +b: String
  {Laws.shape(a ++ b) == Laws.shape(a) ++ Laws.shape(b) : String}

def shape_app(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, x => SCon{Laws.shape.char(h), x},
        Laws.shape(t ++ b), Laws.shape(t) ++ Laws.shape(b), shape_app(t, b))

# the shape of a date
law ymd_shape:
  for +y: U32
  for +m: U32
  for +d: U32
  {Laws.shape(Clock.time.ymd(y, m, d)) == "####-##-##" : String}

def ymd_shape(y, m, d):
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((y / 1000 : U32))), '#',
    digit_shape((y / 1000 : U32)))
    : {SCon{_, SCon{Laws.shape.char(Clock.time.digit((y / 100 : U32))),
      SCon{Laws.shape.char(Clock.time.digit((y / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit(y)), SCon{'-',
          SCon{Laws.shape.char(Clock.time.digit((m / 10 : U32))),
            SCon{Laws.shape.char(Clock.time.digit(m)), SCon{'-',
              SCon{Laws.shape.char(Clock.time.digit((d / 10 : U32))),
                SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((y / 100 : U32))), '#',
    digit_shape((y / 100 : U32)))
    : {SCon{'#', SCon{_, SCon{Laws.shape.char(Clock.time.digit((y / 10 : U32))),
      SCon{Laws.shape.char(Clock.time.digit(y)), SCon{'-',
        SCon{Laws.shape.char(Clock.time.digit((m / 10 : U32))),
          SCon{Laws.shape.char(Clock.time.digit(m)), SCon{'-',
            SCon{Laws.shape.char(Clock.time.digit((d / 10 : U32))),
              SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((y / 10 : U32))), '#',
    digit_shape((y / 10 : U32)))
    : {SCon{'#', SCon{'#', SCon{_, SCon{Laws.shape.char(Clock.time.digit(y)), SCon{'-',
      SCon{Laws.shape.char(Clock.time.digit((m / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit(m)), SCon{'-',
          SCon{Laws.shape.char(Clock.time.digit((d / 10 : U32))),
            SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(y)), '#', digit_shape(y))
    : {SCon{'#', SCon{'#', SCon{'#', SCon{_, SCon{'-',
      SCon{Laws.shape.char(Clock.time.digit((m / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit(m)), SCon{'-',
          SCon{Laws.shape.char(Clock.time.digit((d / 10 : U32))),
            SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((m / 10 : U32))), '#',
    digit_shape((m / 10 : U32)))
    : {SCon{'#', SCon{'#', SCon{'#', SCon{'#', SCon{'-', SCon{_,
      SCon{Laws.shape.char(Clock.time.digit(m)), SCon{'-',
        SCon{Laws.shape.char(Clock.time.digit((d / 10 : U32))),
          SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(m)), '#', digit_shape(m))
    : {SCon{'#', SCon{'#', SCon{'#', SCon{'#', SCon{'-', SCon{'#', SCon{_, SCon{'-',
      SCon{Laws.shape.char(Clock.time.digit((d / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((d / 10 : U32))), '#',
    digit_shape((d / 10 : U32)))
    : {SCon{'#', SCon{'#', SCon{'#', SCon{'#', SCon{'-', SCon{'#', SCon{'#', SCon{'-', SCon{_,
      SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(d)), '#', digit_shape(d))
    : {SCon{'#', SCon{'#', SCon{'#', SCon{'#', SCon{'-', SCon{'#', SCon{'#', SCon{'-', SCon{'#',
      SCon{_, SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  {==}

# the shape of the date of any year, month and day
law ymd_of_shape:
  for date: Clock.Ymd
  {Laws.shape(Clock.time.ymd.of(date)) == "####-##-##" : String}

def ymd_of_shape(date):
  match date:
    case Clock.Ymd{+y, +m, +d}:
      ymd_shape(y, m, d)

# the shape of a time of day
law clock_shape:
  for +sod: U32
  for +ms: U32
  {Laws.shape(Clock.time.clock(sod, ms)) == "##:##:##.###Z" : String}

def clock_shape(sod, ms):
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(((sod / 3600 : U32) / 10 : U32))), '#',
    digit_shape(((sod / 3600 : U32) / 10 : U32)))
    : {SCon{_, SCon{Laws.shape.char(Clock.time.digit((sod / 3600 : U32))), SCon{':',
      SCon{Laws.shape.char(Clock.time.digit(((sod % 3600 / 60 : U32) / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit((sod % 3600 / 60 : U32))), SCon{':',
          SCon{Laws.shape.char(Clock.time.digit(((sod % 60 : U32) / 10 : U32))),
            SCon{Laws.shape.char(Clock.time.digit((sod % 60 : U32))), SCon{'.',
              SCon{Laws.shape.char(Clock.time.digit((ms / 100 : U32))),
                SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
                  SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((sod / 3600 : U32))), '#',
    digit_shape((sod / 3600 : U32)))
    : {SCon{'#', SCon{_, SCon{':',
      SCon{Laws.shape.char(Clock.time.digit(((sod % 3600 / 60 : U32) / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit((sod % 3600 / 60 : U32))), SCon{':',
          SCon{Laws.shape.char(Clock.time.digit(((sod % 60 : U32) / 10 : U32))),
            SCon{Laws.shape.char(Clock.time.digit((sod % 60 : U32))), SCon{'.',
              SCon{Laws.shape.char(Clock.time.digit((ms / 100 : U32))),
                SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
                  SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(((sod % 3600 / 60 : U32) / 10 : U32))), '#',
    digit_shape(((sod % 3600 / 60 : U32) / 10 : U32)))
    : {SCon{'#', SCon{'#', SCon{':', SCon{_,
      SCon{Laws.shape.char(Clock.time.digit((sod % 3600 / 60 : U32))), SCon{':',
        SCon{Laws.shape.char(Clock.time.digit(((sod % 60 : U32) / 10 : U32))),
          SCon{Laws.shape.char(Clock.time.digit((sod % 60 : U32))), SCon{'.',
            SCon{Laws.shape.char(Clock.time.digit((ms / 100 : U32))),
              SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
                SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((sod % 3600 / 60 : U32))), '#',
    digit_shape((sod % 3600 / 60 : U32)))
    : {SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{_, SCon{':',
      SCon{Laws.shape.char(Clock.time.digit(((sod % 60 : U32) / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit((sod % 60 : U32))), SCon{'.',
          SCon{Laws.shape.char(Clock.time.digit((ms / 100 : U32))),
            SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
              SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(((sod % 60 : U32) / 10 : U32))), '#',
    digit_shape(((sod % 60 : U32) / 10 : U32)))
    : {SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{':', SCon{_,
      SCon{Laws.shape.char(Clock.time.digit((sod % 60 : U32))), SCon{'.',
        SCon{Laws.shape.char(Clock.time.digit((ms / 100 : U32))),
          SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
            SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((sod % 60 : U32))), '#',
    digit_shape((sod % 60 : U32)))
    : {SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{_, SCon{'.',
      SCon{Laws.shape.char(Clock.time.digit((ms / 100 : U32))),
        SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
          SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((ms / 100 : U32))), '#',
    digit_shape((ms / 100 : U32)))
    : {SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{'.',
      SCon{_, SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((ms / 10 : U32))), '#',
    digit_shape((ms / 10 : U32)))
    : {SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{'.',
      SCon{'#', SCon{_, SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(ms)), '#', digit_shape(ms))
    : {SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{'.',
      SCon{'#', SCon{'#', SCon{_, SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  {==}

def Laws.iso_shape(secs, ms):
  Equal.trans(String,
    Laws.shape(Clock.time.iso(secs, ms)),
    Laws.shape(Clock.time.date((secs / 86400 : U32)))
      ++ SCon{'T', Laws.shape(Clock.time.clock((secs % 86400 : U32), ms))},
    "####-##-##T##:##:##.###Z",
    shape_app(Clock.time.date((secs / 86400 : U32)),
      SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}),
    Equal.trans(String,
      Laws.shape(Clock.time.date((secs / 86400 : U32)))
        ++ SCon{'T', Laws.shape(Clock.time.clock((secs % 86400 : U32), ms))},
      "####-##-##"
        ++ SCon{'T', Laws.shape(Clock.time.clock((secs % 86400 : U32), ms))},
      "####-##-##T##:##:##.###Z",
      Equal.cong(String, String,
        x => x ++ SCon{'T',
          Laws.shape(Clock.time.clock((secs % 86400 : U32), ms))},
        Laws.shape(Clock.time.date((secs / 86400 : U32))), "####-##-##",
        ymd_of_shape(Clock.time.civil((secs / 86400 : U32)))),
      Equal.cong(String, String, x => "####-##-##" ++ SCon{'T', x},
        Laws.shape(Clock.time.clock((secs % 86400 : U32), ms)),
        "##:##:##.###Z", clock_shape((secs % 86400 : U32), ms))))
