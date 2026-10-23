# ezsys: the laws. Each law carries the SPEC.md row it proves, or proves part
# of, on its own comment line. PROOF.bend fills them; `bend PROOF.bend` is
# the gate. Only the pure modules are imported: src/sys.bend holds foreign
# code, and no file that reaches it can print ALL PROOFS CHECK.
import Base
import ./src/step.bend as Step
import ./src/clock.bend as Clock
import ./src/text.bend as Text

# --- the specification's own words ---

# an ASCII digit becomes '#', any other character stays
def shape.char(chr: Char) -> Char:
  match chr:
    case Chr{+x}:
      Bool.pick(Char, Bool.and((x >= 48 : U32), (x <= 57 : U32)), '#', Chr{x})

# a text with every ASCII digit made '#'
def shape(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{hd, tl}:
      SCon{shape.char(hd), shape(tl)}

# the form of every time.iso
def shape.iso() -> String:
  "####-##-##T##:##:##.###Z"

# --- files (SYS-FILE) ---

# LAW: a read that fails stops with its failure unchanged
# SYS-FILE-1
law read_fail:
  for code: U32
  for why: String
  for got: String
  {Step.read.step(Fail{(code, why)}, got) == Step.ReadStop{Fail{(code, why)}}
    : Step.Read}

# LAW: an empty chunk stops with exactly the text read before it
# SYS-FILE-1
law read_end:
  for got: String
  {Step.read.step(Done{""}, got) == Step.ReadStop{Done{got}} : Step.Read}

# LAW: any other chunk is appended to the text read before it
# SYS-FILE-1
law read_more:
  for h: Char
  for t: String
  for got: String
  {Step.read.step(Done{SCon{h, t}}, got) == Step.ReadMore{got ++ SCon{h, t}}
    : Step.Read}

# LAW: file.save writes to the path with .tmp after it
# SYS-FILE-2
law save_tmp:
  for path: String
  {Step.save.tmp(path) == path ++ ".tmp" : String}

# LAW: a failed write of the temporary file is the answer, and nothing is
# renamed
# SYS-FILE-2
law save_fail:
  for code: U32
  for why: String
  {Step.save.step(Fail{(code, why)}) == Step.SaveStop{(code, why)} : Step.Save}

# LAW: a written temporary file is renamed
# SYS-FILE-2
law save_move:
  for u: Unit
  {Step.save.step(Done{u}) == Step.SaveMove{} : Step.Save}

# --- environment (SYS-ENV) ---

# LAW: a set variable's value is the answer, even an empty one
# SYS-ENV-1
law env_set:
  for value: String
  for fallback: String
  {Step.env.pick(Done{value}, fallback) == value : String}

# LAW: an unset variable answers the fallback
# SYS-ENV-1
law env_unset:
  for code: U32
  for why: String
  for fallback: String
  {Step.env.pick(Fail{(code, why)}, fallback) == fallback : String}

# --- wall clock (SYS-TIME) ---

# LAW: every time.iso has the form ####-##-##T##:##:##.###Z, # a digit
# SYS-TIME-1
law iso_shape:
  for +secs: U32
  for +ms: U32
  {shape(Clock.time.iso(secs, ms)) == shape.iso() : String}

# LAW: every time.iso is 24 characters
# SYS-TIME-1
law iso_width:
  for secs: U32
  for ms: U32
  {String.length(Clock.time.iso(secs, ms)) == 24n : Nat}

# LAW: the date is the day's, then T and the time of day
# SYS-TIME-2
law iso_split:
  for secs: U32
  for ms: U32
  {Clock.time.iso(secs, ms) == Clock.time.date((secs / 86400 : U32))
    ++ "T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: the time of day is hours, minutes and seconds of the second of the
# day, then the milliseconds
# SYS-TIME-2
law clock_fields:
  for sod: U32
  for ms: U32
  {Clock.time.clock(sod, ms) == Clock.time.two((sod / 3600 : U32)) ++ ":"
    ++ Clock.time.two((sod % 3600 / 60 : U32)) ++ ":"
    ++ Clock.time.two((sod % 60 : U32)) ++ "." ++ Clock.time.three(ms) ++ "Z"
    : String}

# LAW: the date is four digits of the year, two of the month and two of the
# day of the day number
# SYS-TIME-2
law date_fields:
  for days: U32
  {Clock.time.date(days) == Clock.time.ymd.of(Clock.time.civil(days))
    : String}

# LAW: day 11016 is 2000-02-29, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law leap_2000:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 11016 : U32}
  {Clock.time.iso(secs, ms)
    == "2000-02-29T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 11017 is 2000-03-01, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law leap_2000_after:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 11017 : U32}
  {Clock.time.iso(secs, ms)
    == "2000-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 19782 is 2024-02-29, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law leap_2024:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 19782 : U32}
  {Clock.time.iso(secs, ms)
    == "2024-02-29T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 19783 is 2024-03-01, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law leap_2024_after:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 19783 : U32}
  {Clock.time.iso(secs, ms)
    == "2024-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 19416 is 2023-02-28, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law common_2023:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 19416 : U32}
  {Clock.time.iso(secs, ms)
    == "2023-02-28T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 19417 is 2023-03-01, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law common_2023_after:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 19417 : U32}
  {Clock.time.iso(secs, ms)
    == "2023-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 47540 is 2100-02-28, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law century_2100:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 47540 : U32}
  {Clock.time.iso(secs, ms)
    == "2100-02-28T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 47541 is 2100-03-01, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law century_2100_after:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 47541 : U32}
  {Clock.time.iso(secs, ms)
    == "2100-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 0 is 1970-01-01, at every second of it
# SYS-TIME-4
# SYS-TIME-5
law epoch:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 0 : U32}
  {Clock.time.iso(secs, ms)
    == "1970-01-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 10956 is 1999-12-31, at every second of it
# SYS-TIME-4
# SYS-TIME-5
law eve_2000:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 10956 : U32}
  {Clock.time.iso(secs, ms)
    == "1999-12-31T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 10957 is 2000-01-01, at every second of it
# SYS-TIME-4
# SYS-TIME-5
law day_2000:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 10957 : U32}
  {Clock.time.iso(secs, ms)
    == "2000-01-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 49710 is 2106-02-07, at every second of it
# SYS-TIME-4
# SYS-TIME-5
law last_day:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 49710 : U32}
  {Clock.time.iso(secs, ms)
    == "2106-02-07T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: the last second a U32 holds is 2106-02-07T06:28:15
# SYS-TIME-4
law last_second:
  for ms: U32
  {Clock.time.iso(4294967295, ms)
    == "2106-02-07T06:28:15." ++ Clock.time.three(ms) ++ "Z" : String}

# --- text templates (SYS-TEXT) ---

# LAW: a template with no open delimiter in it is unchanged
# SYS-TEXT-1
law fill_unmarked:
  for open: String
  for close: String
  for t: String
  for pairs: Text.text.Pairs()
  for e: {Text.text.marked(open, t) == False{} : Bool}
  {Text.text.fill_with(open, close, t, pairs) == t : String}

# LAW: an empty open delimiter marks nothing
# SYS-TEXT-1
law fill_open_empty:
  for close: String
  for t: String
  for pairs: Text.text.Pairs()
  {Text.text.fill_with("", close, t, pairs) == t : String}

# LAW: an empty close delimiter marks nothing
# SYS-TEXT-1
law fill_close_empty:
  for open: String
  for t: String
  for pairs: Text.text.Pairs()
  {Text.text.fill_with(open, "", t, pairs) == t : String}

# LAW: a character where no open delimiter starts is written as it is
# SYS-TEXT-2
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

# LAW: a marker whose key has a value is replaced by exactly that value
# SYS-TEXT-3
law fill_known:
  for +oh: Char
  for +ot: String
  for +ch: Char
  for +ct: String
  for +key: String
  for +value: String
  for +rest: String
  for +pairs: Text.text.Pairs()
  for +found: {Text.text.value(pairs, key) == Some{value} : Maybe<&2, String>}
  for +free: {Text.text.free(SCon{ch, ct}, key, SCon{ch, ct} ++ rest) == True{}
    : Bool}
  {Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct},
    SCon{oh, ot} ++ (key ++ (SCon{ch, ct} ++ rest)), pairs)
    == value ++ Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, rest, pairs)
    : String}

# LAW: a marker whose key has no value is left as written
# SYS-TEXT-4
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

# LAW: a marker with no close delimiter is left as written
# SYS-TEXT-5
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

# LAW: no pairs, no value
# SYS-TEXT-6
law value_none:
  for key: String
  {Text.text.value([], key) == None{} : Maybe<&2, String>}

# LAW: the first pair with the key gives its value
# SYS-TEXT-6
law value_hit:
  for k: String
  for v: String
  for rest: Text.text.Pairs()
  for key: String
  for e: {String.eq(k, key) == True{} : Bool}
  {Text.text.value((k, v) <> rest, key) == Some{v} : Maybe<&2, String>}

# LAW: a pair with another key is passed over
# SYS-TEXT-6
law value_miss:
  for k: String
  for v: String
  for rest: Text.text.Pairs()
  for key: String
  for e: {String.eq(k, key) == False{} : Bool}
  {Text.text.value((k, v) <> rest, key) == Text.text.value(rest, key)
    : Maybe<&2, String>}

# LAW: the caller's pairs are kept in their order
# SYS-TEXT-6
law own_order:
  for k: String
  for v: String
  for rest: List<(String & String)>
  {Text.text.own((k, v) <> rest) == (k, v) <> Text.text.own(rest)
    : Text.text.Pairs()}

# LAW: text.fill is text.fill_with with {{ and }}
# SYS-TEXT-7
law fill_braces:
  for t: String
  for pairs: Text.text.Pairs()
  {Text.text.fill(t, pairs) == Text.text.fill_with("{{", "}}", t, pairs)
    : String}
