# ezsys: the laws. Each law carries the SPEC.md row it proves, or proves part
# of, on its own comment line. PROOF.bend fills them; `bend PROOF.bend` is
# the gate. Only the pure modules are imported: src/sys.bend holds foreign
# code, and no file that reaches it can print ALL PROOFS CHECK.
import Base
import ./src/step.bend as Step
import ./src/clock.bend as Clock
import ./src/text.bend as Text
import ./src/dir.bend as Dir
import ./src/errno.bend as Err
import ./src/str.bend as Str

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

# --- weekdays and ISO 8601 weeks (SYS-TIME) ---

# the weekday of the civil fields
def wday(fields: U32 & U32 & U32 & U32 & U32 & U32 & U32) -> U32:
  (_y, _mo, _d, _h, _mi, _s, wd) = fields
  wd

# the civil fields written as time.iso writes them, with a millisecond
def civil_text(
  fields: U32 & U32 & U32 & U32 & U32 & U32 & U32,
  ms: U32
) -> String:
  (year, month, day, hour, minute, second, _wd) = fields
  Clock.time.four(year) ++ "-" ++ Clock.time.two(month) ++ "-"
    ++ Clock.time.two(day) ++ "T" ++ Clock.time.two(hour) ++ ":"
    ++ Clock.time.two(minute) ++ ":" ++ Clock.time.two(second) ++ "."
    ++ Clock.time.three(ms) ++ "Z"

# LAW: every second of 1970-01-01 is a Thursday, ISO weekday 4
# SYS-TIME-6
law weekday_epoch:
  for secs: U32
  for e: {(secs / 86400 : U32) == 0 : U32}
  {Clock.time.weekday((secs / 86400 : U32)) == 4 : U32}

# LAW: each day's day of the week is the one after the day before's
# SYS-TIME-6
law weekday_step:
  for num: Nat
  {Clock.time.wd.go(1n+num, Clock.Thu{})
    == Clock.time.wd.next(Clock.time.wd.go(num, Clock.Thu{})) : Clock.Wd}

# LAW: the weekday number after 7 (Sunday) is 1 (Monday); after any other,
# the next number
# SYS-TIME-6
law weekday_next:
  for day: Clock.Wd
  {Clock.time.wd.num(Clock.time.wd.next(day))
    == Bool.pick(U32, U32.is_eq(Clock.time.wd.num(day), 7), 1,
      (Clock.time.wd.num(day) + 1 : U32)) : U32}

# LAW: the weekday of day n is the number of the day of the week n days
# after 1970-01-01, a Thursday
# SYS-TIME-6
law weekday_nat:
  for num: Nat
  {Clock.time.weekday.nat(num)
    == Clock.time.wd.num(Clock.time.wd.go(num, Clock.Thu{})) : U32}

# LAW: a day number's weekday, computed a bit at a time, is that of the day
# that many days after 1970-01-01, counted a day at a time
# SYS-TIME-6
law weekday_days:
  for days: U32
  {Clock.time.weekday(days) == Clock.time.weekday.nat(U32.to_nat(days)) : U32}

# LAW: time.civil's weekday is its day's
# SYS-TIME-6
law fields_weekday:
  for +secs: U32
  {wday(Clock.time.fields(secs)) == Clock.time.weekday((secs / 86400 : U32))
    : U32}

# LAW: the civil fields are the ones time.iso writes
# SYS-TIME-7
law civil_iso:
  for +secs: U32
  for +ms: U32
  {Clock.time.iso(secs, ms) == civil_text(Clock.time.fields(secs), ms)
    : String}

# LAW: a day's ISO year and week are its week's Thursday's calendar year and
# how many Thursdays of that year it is
# SYS-TIME-8
law week_rule:
  for +secs: U32
  {Clock.time.iso_week(secs)
    == Clock.time.week.of(Clock.time.thursday((secs / 86400 : U32)),
      Clock.time.civil(Clock.time.thursday((secs / 86400 : U32))))
    : U32 & U32}

# LAW: a week's Thursday is 4 less the weekday days on, Monday to Sunday
# SYS-TIME-8
law thursday_def:
  for +days: U32
  {Clock.time.thursday(days) == (days + 4 - Clock.time.weekday(days) : U32)
    : U32}

# LAW: the week of a Thursday is one more than the whole weeks since 1
# January of its year
# SYS-TIME-8
law week_of_def:
  for +thu: U32
  for +year: U32
  for month: U32
  for day: U32
  {Clock.time.week.of(thu, Clock.Ymd{year, month, day})
    == (year, ((thu - Clock.time.jan1(year)) / 7 + 1 : U32)) : U32 & U32}

# LAW: the text of a year and week is YYYY-Www, the week in two digits
# SYS-TIME-8
law week_text:
  for year: U32
  for num: U32
  {Clock.time.week.text((year, num))
    == Clock.time.four(year) ++ "-W" ++ Clock.time.two(num) : String}

# LAW: iso_week_text writes iso_week
# SYS-TIME-8
law week_text_of:
  for +secs: U32
  {Clock.time.iso_week_text(secs)
    == Clock.time.week.text(Clock.time.iso_week(secs)) : String}

# LAW: every second of 2008-12-29 is written 2009-W01, the week zero-padded
# SYS-TIME-8
# SYS-TIME-9
law week_text_2009:
  for secs: U32
  for e: {(secs / 86400 : U32) == 14242 : U32}
  {Clock.time.iso_week_text(secs) == "2009-W01" : String}

# LAW: every second of 2008-12-29 (Monday) is in week 1 of 2009
# SYS-TIME-9
# SYS-TIME-11
law week_dec29_2008:
  for secs: U32
  for e: {(secs / 86400 : U32) == 14242 : U32}
  {Clock.time.iso_week(secs) == (2009, 1) : U32 & U32}

# LAW: every second of 2014-12-31 (Wednesday) is in week 1 of 2015
# SYS-TIME-9
# SYS-TIME-11
law week_dec31_2014:
  for secs: U32
  for e: {(secs / 86400 : U32) == 16435 : U32}
  {Clock.time.iso_week(secs) == (2015, 1) : U32 & U32}

# LAW: every second of 2019-12-30 (Monday) is in week 1 of 2020
# SYS-TIME-9
# SYS-TIME-11
law week_dec30_2019:
  for secs: U32
  for e: {(secs / 86400 : U32) == 18260 : U32}
  {Clock.time.iso_week(secs) == (2020, 1) : U32 & U32}

# LAW: every second of 2024-12-31 (Tuesday) is in week 1 of 2025
# SYS-TIME-9
# SYS-TIME-11
law week_dec31_2024:
  for secs: U32
  for e: {(secs / 86400 : U32) == 20088 : U32}
  {Clock.time.iso_week(secs) == (2025, 1) : U32 & U32}

# LAW: every second of 2010-01-03 (Sunday) is in week 53 of 2009
# SYS-TIME-9
# SYS-TIME-11
law week_jan3_2010:
  for secs: U32
  for e: {(secs / 86400 : U32) == 14612 : U32}
  {Clock.time.iso_week(secs) == (2009, 53) : U32 & U32}

# LAW: every second of 2016-01-01 (Friday) is in week 53 of 2015
# SYS-TIME-9
# SYS-TIME-11
law week_jan1_2016:
  for secs: U32
  for e: {(secs / 86400 : U32) == 16801 : U32}
  {Clock.time.iso_week(secs) == (2015, 53) : U32 & U32}

# LAW: every second of 2021-01-03 (Sunday) is in week 53 of 2020
# SYS-TIME-9
# SYS-TIME-11
law week_jan3_2021:
  for secs: U32
  for e: {(secs / 86400 : U32) == 18630 : U32}
  {Clock.time.iso_week(secs) == (2020, 53) : U32 & U32}

# LAW: every second of 2022-01-01 (Saturday) is in week 52 of 2021
# SYS-TIME-9
# SYS-TIME-11
law week_jan1_2022:
  for secs: U32
  for e: {(secs / 86400 : U32) == 18993 : U32}
  {Clock.time.iso_week(secs) == (2021, 52) : U32 & U32}

# LAW: every second of 2023-01-01 (Sunday) is in week 52 of 2022
# SYS-TIME-9
# SYS-TIME-11
law week_jan1_2023:
  for secs: U32
  for e: {(secs / 86400 : U32) == 19358 : U32}
  {Clock.time.iso_week(secs) == (2022, 52) : U32 & U32}

# LAW: every second of 2027-01-01 (Friday) is in week 53 of 2026
# SYS-TIME-9
# SYS-TIME-11
law week_jan1_2027:
  for secs: U32
  for e: {(secs / 86400 : U32) == 20819 : U32}
  {Clock.time.iso_week(secs) == (2026, 53) : U32 & U32}

# LAW: every second of 2020-12-31 (Thursday) is in week 53 of 2020
# SYS-TIME-10
# SYS-TIME-11
law week_53_2020:
  for secs: U32
  for e: {(secs / 86400 : U32) == 18627 : U32}
  {Clock.time.iso_week(secs) == (2020, 53) : U32 & U32}

# LAW: every second of 2026-12-31 (Thursday) is in week 53 of 2026
# SYS-TIME-10
# SYS-TIME-11
law week_53_2026:
  for secs: U32
  for e: {(secs / 86400 : U32) == 20818 : U32}
  {Clock.time.iso_week(secs) == (2026, 53) : U32 & U32}

# LAW: every second of 2021-12-31 (Friday) is in week 52 of 2021
# SYS-TIME-10
# SYS-TIME-11
law week_52_2021:
  for secs: U32
  for e: {(secs / 86400 : U32) == 18992 : U32}
  {Clock.time.iso_week(secs) == (2021, 52) : U32 & U32}

# LAW: every second of 2025-12-28 (Sunday) is in week 52 of 2025
# SYS-TIME-10
# SYS-TIME-11
law week_52_2025:
  for secs: U32
  for e: {(secs / 86400 : U32) == 20450 : U32}
  {Clock.time.iso_week(secs) == (2025, 52) : U32 & U32}

# LAW: every second of 2025-12-29 (Monday) is in week 1 of 2026
# SYS-TIME-10
# SYS-TIME-11
law week_after_52_2025:
  for secs: U32
  for e: {(secs / 86400 : U32) == 20451 : U32}
  {Clock.time.iso_week(secs) == (2026, 1) : U32 & U32}

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

# --- directories (SYS-DIR) ---

# one copy of the name, when hit holds
def listed.pick(hit: Bool, count: Nat) -> Nat:
  match hit:
    case True{}:
      1n+count
    case False{}:
      count

# how many times a list holds a name
def listed(+name: String, xs: List<&2, String>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      listed.pick(String.eq(x, name), listed(name, rest))

# whether every name after prev is no greater than the one before it
def ascending.from(xs: List<&2, String>, +prev: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(String.is_le(prev, y), ascending.from(rest, y))

# whether every name is no greater by String.order than the one after it
def ascending(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      ascending.from(rest, x)

# LAW: a name that is neither . nor .. is answered as many times as the raw
# names hold it, and . and .. never
# SYS-DIR-1
law dir_count:
  for +raw: List<&2, String>
  for +name: String
  {listed(name, Dir.dir.names(raw))
    == Bool.pick(Nat, Bool.or(String.eq(name, "."), String.eq(name, "..")),
      0n, listed(name, raw)) : Nat}

# LAW: the answer is ascending by String.order
# SYS-DIR-2
law dir_sorted:
  for raw: List<&2, String>
  {ascending(Dir.dir.names(raw)) == True{} : Bool}

# LAW: a failed directory read is the answer unchanged
# SYS-DIR-3
law dir_fail:
  for code: U32
  for why: String
  {Dir.dir.step(Fail{(code, why)}) == Fail{(code, why)}
    : Result<&1, &1, U32 & String, List<&2, String>>}

# LAW: a directory read's names are answered as dir.names gives them
# SYS-DIR-3
law dir_done:
  for raw: List<&2, String>
  {Dir.dir.step(Done{raw}) == Done{Dir.dir.names(raw)}
    : Result<&1, &1, U32 & String, List<&2, String>>}

# --- errors (SYS-ERR) ---

# the common Linux codes and glibc's text for each, as Python's os.strerror
# gives it
def strerror() -> Err.err.Table():
  [
    (1, "Operation not permitted"),
    (2, "No such file or directory"),
    (3, "No such process"),
    (4, "Interrupted system call"),
    (5, "Input/output error"),
    (6, "No such device or address"),
    (7, "Argument list too long"),
    (8, "Exec format error"),
    (9, "Bad file descriptor"),
    (10, "No child processes"),
    (11, "Resource temporarily unavailable"),
    (12, "Cannot allocate memory"),
    (13, "Permission denied"),
    (14, "Bad address"),
    (15, "Block device required"),
    (16, "Device or resource busy"),
    (17, "File exists"),
    (18, "Invalid cross-device link"),
    (19, "No such device"),
    (20, "Not a directory"),
    (21, "Is a directory"),
    (22, "Invalid argument"),
    (23, "Too many open files in system"),
    (24, "Too many open files"),
    (25, "Inappropriate ioctl for device"),
    (26, "Text file busy"),
    (27, "File too large"),
    (28, "No space left on device"),
    (29, "Illegal seek"),
    (30, "Read-only file system"),
    (31, "Too many links"),
    (32, "Broken pipe"),
    (33, "Numerical argument out of domain"),
    (34, "Numerical result out of range"),
    (35, "Resource deadlock avoided"),
    (36, "File name too long"),
    (37, "No locks available"),
    (38, "Function not implemented"),
    (39, "Directory not empty"),
    (40, "Too many levels of symbolic links"),
    (84, "Invalid or incomplete multibyte or wide character"),
    (95, "Operation not supported"),
    (110, "Connection timed out"),
    (111, "Connection refused"),
    (112, "Host is down"),
    (113, "No route to host"),
    (116, "Stale file handle"),
    (122, "Disk quota exceeded"),
    (125, "Operation canceled")
  ]

# the hex digit at a place of "0123456789abcdef", '0' past it
def hexc(place: U32) -> Char:
  Err.err.hex.or(String.get("0123456789abcdef", U32.to_nat(place)))

# LAW: a code's text is looked up in strerror, with why for a code it lacks
# SYS-ERR-1
law err_table:
  for +code: U32
  for +why: String
  {Err.err.text(code, why) == Err.err.look(strerror(), code, why) : String}

# LAW: a code no entry has is written with why
# SYS-ERR-1
law look_none:
  for +code: U32
  for +why: String
  {Err.err.look(Nil{}, code, why) == why : String}

# LAW: the first entry with the code gives its text
# SYS-ERR-1
law look_hit:
  for k: U32
  for text: String
  for rest: Err.err.Table()
  for +code: U32
  for +why: String
  for e: {U32.is_eq(code, k) == True{} : Bool}
  {Err.err.look(Con{(k, text), rest}, code, why) == text : String}

# LAW: an entry with another code is passed over
# SYS-ERR-1
law look_miss:
  for k: U32
  for text: String
  for rest: Err.err.Table()
  for +code: U32
  for +why: String
  for e: {U32.is_eq(code, k) == False{} : Bool}
  {Err.err.look(Con{(k, text), rest}, code, why)
    == Err.err.look(rest, code, why) : String}

# LAW: [Errno N] text: repr(path)
# SYS-ERR-2
law err_os:
  for +code: U32
  for +why: String
  for +path: String
  {Err.err.os(code, why, path) == "[Errno " ++ U32.show(code) ++ "] "
    ++ Err.err.text(code, why) ++ ": " ++ Err.err.repr(path) : String}

# LAW: repr is the quote, the escaped characters and the quote
# SYS-ERR-3
law repr_shape:
  for +path: String
  {Err.err.repr(path) == SCon{Err.err.quote(path),
    Err.err.go(Err.err.quote(path), path)
      ++ SCon{Err.err.quote(path), SNil{}}} : String}

# LAW: a path with a ' and no " is quoted with "
# SYS-ERR-3
law quote_double:
  for +path: String
  for one: {String.contains(path, "'") == True{} : Bool}
  for two: {String.contains(path, "\"") == False{} : Bool}
  {Err.err.quote(path) == '"' : Char}

# LAW: a path with no ' is quoted with '
# SYS-ERR-3
law quote_plain:
  for +path: String
  for e: {String.contains(path, "'") == False{} : Bool}
  {Err.err.quote(path) == '\'' : Char}

# LAW: a path with a " is quoted with '
# SYS-ERR-3
law quote_both:
  for +path: String
  for e: {String.contains(path, "\"") == True{} : Bool}
  {Err.err.quote(path) == '\'' : Char}

# LAW: no characters are written as nothing
# SYS-ERR-3
law go_empty:
  for +q: Char
  {Err.err.go(q, "") == "" : String}

# LAW: the characters are escaped one by one, in order
# SYS-ERR-3
law go_char:
  for +q: Char
  for c: Char
  for t: String
  {Err.err.go(q, SCon{c, t}) == Err.err.esc(q, c) ++ Err.err.go(q, t)
    : String}

# LAW: a tab is written \t
# SYS-ERR-3
law esc_tab:
  for +q: Char
  {Err.err.esc(q, '\t') == "\\t" : String}

# LAW: a newline is written \n
# SYS-ERR-3
law esc_newline:
  for +q: Char
  {Err.err.esc(q, '\n') == "\\n" : String}

# LAW: a carriage return is written \r
# SYS-ERR-3
law esc_return:
  for +q: Char
  {Err.err.esc(q, '\r') == "\\r" : String}

# LAW: every other code point below U+0020, U+007F to U+00A0, and U+00AD is
# written \x and two hex digits
# SYS-ERR-3
law esc_hex:
  for +q: Char
  for +x: U32
  for set: {Bool.or(U32.is_lt(x, 32), Bool.or(Bool.and(U32.is_ge(x, 127),
    U32.is_le(x, 160)), U32.is_eq(x, 173))) == True{} : Bool}
  for tab: {U32.is_eq(x, 9) == False{} : Bool}
  for nl: {U32.is_eq(x, 10) == False{} : Bool}
  for cr: {U32.is_eq(x, 13) == False{} : Bool}
  {Err.err.esc(q, Chr{x}) == "\\x" ++ Err.err.hex2(x) : String}

# LAW: the two hex digits are lowercase, the high four bits first
# SYS-ERR-3
law hex_pair:
  for +x: U32
  {Err.err.hex2(x) == SCon{hexc(((x / 16 : U32) % 16 : U32)),
    SCon{hexc((x % 16 : U32)), SNil{}}} : String}

# LAW: a backslash is written twice
# SYS-ERR-3
law esc_backslash:
  for +q: Char
  {Err.err.esc(q, '\\') == "\\\\" : String}

# LAW: the chosen quote is written after a backslash
# SYS-ERR-3
law esc_quote:
  for +q: Char
  for +x: U32
  for set: {Bool.or(U32.is_lt(x, 32), Bool.or(Bool.and(U32.is_ge(x, 127),
    U32.is_le(x, 160)), U32.is_eq(x, 173))) == False{} : Bool}
  for bs: {U32.is_eq(x, 92) == False{} : Bool}
  for hit: {Char.is_eq(Chr{x}, q) == True{} : Bool}
  {Err.err.esc(q, Chr{x}) == SCon{'\\', SCon{q, SNil{}}} : String}

# LAW: every other character is written as itself
# SYS-ERR-3
law esc_plain:
  for +q: Char
  for +x: U32
  for set: {Bool.or(U32.is_lt(x, 32), Bool.or(Bool.and(U32.is_ge(x, 127),
    U32.is_le(x, 160)), U32.is_eq(x, 173))) == False{} : Bool}
  for bs: {U32.is_eq(x, 92) == False{} : Bool}
  for miss: {Char.is_eq(Chr{x}, q) == False{} : Bool}
  {Err.err.esc(q, Chr{x}) == SCon{Chr{x}, SNil{}} : String}

# --- whitespace (SYS-STR) ---

# LAW: a character is whitespace exactly when its code point is one of
# Python's: 9 to 13, 28 to 32, 133, 160, 5760, 8192 to 8202, 8232, 8233,
# 8239, 8287 and 12288
# SYS-STR-1
law space_set:
  for x: U32
  {Str.text.space(Chr{x}) == List.contains(~U32, ~U32.is_eq,
    [9, 10, 11, 12, 13, 28, 29, 30, 31, 32, 133, 160, 5760, 8192, 8193, 8194,
      8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8232, 8233, 8239, 8287,
      12288], x) : Bool}

# LAW: a leading whitespace character is removed, and lstrip goes on
# SYS-STR-2
law lstrip_space:
  for h: Char
  for t: String
  for e: {Str.text.space(h) == True{} : Bool}
  {Str.text.lstrip(SCon{h, t}) == Str.text.lstrip(t) : String}

# LAW: a text that starts with a character that is not whitespace is kept
# SYS-STR-2
law lstrip_keep:
  for h: Char
  for t: String
  for e: {Str.text.space(h) == False{} : Bool}
  {Str.text.lstrip(SCon{h, t}) == SCon{h, t} : String}

# LAW: the empty text is kept
# SYS-STR-2
law lstrip_empty:
  for s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {Str.text.lstrip(s) == s : String}

# LAW: a trailing whitespace character is removed, and rstrip goes on
# SYS-STR-3
law rstrip_space:
  for +t: String
  for +h: Char
  for e: {Str.text.space(h) == True{} : Bool}
  {Str.text.rstrip(t ++ SCon{h, SNil{}}) == Str.text.rstrip(t) : String}

# LAW: a text that ends with a character that is not whitespace is kept
# SYS-STR-3
law rstrip_keep:
  for +t: String
  for +h: Char
  for e: {Str.text.space(h) == False{} : Bool}
  {Str.text.rstrip(t ++ SCon{h, SNil{}}) == t ++ SCon{h, SNil{}} : String}

# LAW: the empty text is kept
# SYS-STR-3
law rstrip_empty:
  for s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {Str.text.rstrip(s) == s : String}

# LAW: strip is rstrip of lstrip
# SYS-STR-3
law strip_both:
  for s: String
  {Str.text.strip(s) == Str.text.rstrip(Str.text.lstrip(s)) : String}

# --- replace, split and find (SYS-STR) ---

# LAW: an `old` at the start is replaced, and the scan goes on after it
# SYS-STR-4
law replace_hit:
  for +oh: Char
  for +ot: String
  for +rest: String
  for +new: String
  {Str.text.replace(SCon{oh, ot} ++ rest, SCon{oh, ot}, new)
    == new ++ Str.text.replace(rest, SCon{oh, ot}, new) : String}

# LAW: a character where no `old` starts is kept, and the scan goes on
# after it
# SYS-STR-4
law replace_miss:
  for +h: Char
  for +t: String
  for +oh: Char
  for +ot: String
  for +new: String
  for e: {String.starts_with(SCon{h, t}, SCon{oh, ot}) == False{} : Bool}
  {Str.text.replace(SCon{h, t}, SCon{oh, ot}, new)
    == SCon{h, Str.text.replace(t, SCon{oh, ot}, new)} : String}

# LAW: replacing in the empty text gives the empty text
# SYS-STR-4
law replace_end:
  for oh: Char
  for ot: String
  for new: String
  {Str.text.replace("", SCon{oh, ot}, new) == "" : String}

# LAW: an empty `old` puts `new` before the first character, and goes on
# SYS-STR-5
law replace_gaps:
  for +h: Char
  for +t: String
  for +new: String
  {Str.text.replace(SCon{h, t}, "", new)
    == new ++ SCon{h, Str.text.replace(t, "", new)} : String}

# LAW: an empty `old` in the empty text gives `new`
# SYS-STR-5
law replace_gaps_end:
  for +new: String
  {Str.text.replace("", "", new) == new : String}

# LAW: the empty text is one empty piece
# SYS-STR-6
law split_end:
  for sh: Char
  for st: String
  {Str.text.split("", SCon{sh, st}) == [""] : List<&2, String>}

# LAW: a separator at the start ends an empty piece, and the scan goes on
# after it
# SYS-STR-6
law split_hit:
  for +sh: Char
  for +st: String
  for +rest: String
  {Str.text.split(SCon{sh, st} ++ rest, SCon{sh, st})
    == SNil{} <> Str.text.split(rest, SCon{sh, st}) : List<&2, String>}

# LAW: a character where no separator starts begins the first piece
# SYS-STR-6
law split_miss:
  for +h: Char
  for +t: String
  for +sh: Char
  for +st: String
  for e: {String.starts_with(SCon{h, t}, SCon{sh, st}) == False{} : Bool}
  {Str.text.split(SCon{h, t}, SCon{sh, st})
    == Str.text.split.push(h, Str.text.split(t, SCon{sh, st}))
    : List<&2, String>}

# LAW: a character pushed on the pieces goes on the front of the first
# SYS-STR-6
law split_push:
  for h: Char
  for p: String
  for ps: List<&2, String>
  {Str.text.split.push(h, p <> ps) == SCon{h, p} <> ps : List<&2, String>}

# LAW: split never answers no pieces
# SYS-STR-6
law split_some:
  for +s: String
  for +sh: Char
  for +st: String
  {List.is_empty(&2, String, Str.text.split(s, SCon{sh, st})) == False{}
    : Bool}

# LAW: an empty separator answers the text as its one piece
# SYS-STR-6
law split_whole:
  for s: String
  {Str.text.split(s, "") == [s] : List<&2, String>}

# LAW: an empty needle is found at 0
# SYS-STR-7
law find_empty:
  for s: String
  {Str.text.find(s, "") == Some{0} : Maybe<&2, U32>}

# LAW: a needle at the start is found at 0
# SYS-STR-7
law find_hit:
  for +h: Char
  for +t: String
  for +needle: String
  for e: {String.starts_with(SCon{h, t}, needle) == True{} : Bool}
  {Str.text.find(SCon{h, t}, needle) == Some{0} : Maybe<&2, U32>}

# LAW: past a character where the needle does not start, a needle found at
# i in the rest is found at i + 1
# SYS-STR-7
law find_next:
  for +h: Char
  for +t: String
  for +needle: String
  for i: U32
  for e: {String.starts_with(SCon{h, t}, needle) == False{} : Bool}
  for got: {Str.text.find(t, needle) == Some{i} : Maybe<&2, U32>}
  {Str.text.find(SCon{h, t}, needle) == Some{(i + 1 : U32)}
    : Maybe<&2, U32>}

# LAW: past a character where the needle does not start, a needle not in
# the rest is not found
# SYS-STR-7
law find_none:
  for +h: Char
  for +t: String
  for +needle: String
  for e: {String.starts_with(SCon{h, t}, needle) == False{} : Bool}
  for got: {Str.text.find(t, needle) == None{} : Maybe<&2, U32>}
  {Str.text.find(SCon{h, t}, needle) == None{} : Maybe<&2, U32>}

# LAW: a nonempty needle is not found in the empty text
# SYS-STR-7
law find_end:
  for nh: Char
  for nt: String
  {Str.text.find("", SCon{nh, nt}) == None{} : Maybe<&2, U32>}

# LAW: find answers a place exactly when Base's String.contains holds
# SYS-STR-8
law find_contains:
  for +s: String
  for +needle: String
  {Maybe.is_some(&2, U32, Str.text.find(s, needle))
    == String.contains(s, needle) : Bool}

# --- case (SYS-CASE) ---

# LAW: lower is the lowercase of the first character, then of the rest
# SYS-CASE-1
law lower_con:
  for h: Char
  for t: String
  {Str.text.lower(SCon{h, t}) == Str.text.lower.char(h) ++ Str.text.lower(t)
    : String}

# LAW: lower keeps the empty text
# SYS-CASE-1
law lower_nil:
  for s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {Str.text.lower(s) == s : String}

# LAW: upper is the uppercase of the first character, then of the rest
# SYS-CASE-1
law upper_con:
  for h: Char
  for t: String
  {Str.text.upper(SCon{h, t}) == Str.text.upper.char(h) ++ Str.text.upper(t)
    : String}

# LAW: upper keeps the empty text
# SYS-CASE-1
law upper_nil:
  for s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {Str.text.upper(s) == s : String}

# LAW: a character's lowercase is given by this table: U+0130 maps to
# U+0069 U+0307, and every rule maps a run of code points in order
# SYS-CASE-2
law lower_table:
  for x: U32
  {Str.text.lower.char(Chr{x}) == Str.text.case.of(
    [Str.Multi{304, "i\u{307}"}],
    [
        Str.Rule{65, 90, 1, 97},
        Str.Rule{192, 214, 1, 224},
        Str.Rule{216, 222, 1, 248},
        Str.Rule{256, 302, 2, 257},
        Str.Rule{306, 310, 2, 307},
        Str.Rule{313, 327, 2, 314},
        Str.Rule{330, 374, 2, 331},
        Str.Rule{376, 376, 1, 255},
        Str.Rule{377, 381, 2, 378},
        Str.Rule{880, 882, 2, 881},
        Str.Rule{886, 886, 1, 887},
        Str.Rule{895, 895, 1, 1011},
        Str.Rule{902, 902, 1, 940},
        Str.Rule{904, 906, 1, 941},
        Str.Rule{908, 908, 1, 972},
        Str.Rule{910, 911, 1, 973},
        Str.Rule{913, 929, 1, 945},
        Str.Rule{931, 939, 1, 963},
        Str.Rule{975, 975, 1, 983},
        Str.Rule{984, 1006, 2, 985},
        Str.Rule{1012, 1012, 1, 952},
        Str.Rule{1015, 1015, 1, 1016},
        Str.Rule{1017, 1017, 1, 1010},
        Str.Rule{1018, 1018, 1, 1019},
        Str.Rule{1021, 1023, 1, 891},
        Str.Rule{1024, 1039, 1, 1104},
        Str.Rule{1040, 1071, 1, 1072},
        Str.Rule{1120, 1152, 2, 1121},
        Str.Rule{1162, 1214, 2, 1163},
        Str.Rule{1216, 1216, 1, 1231},
        Str.Rule{1217, 1229, 2, 1218},
        Str.Rule{1232, 1278, 2, 1233}
      ], x) : String}

# LAW: a character's uppercase is given by this table: U+00DF, U+0149,
# U+0390 and U+03B0 map to more than one code point, and every rule maps a
# run of code points in order
# SYS-CASE-2
law upper_table:
  for x: U32
  {Str.text.upper.char(Chr{x}) == Str.text.case.of(
    [
        Str.Multi{223, "SS"},
        Str.Multi{329, "\u{2BC}N"},
        Str.Multi{912, "\u{399}\u{308}\u{301}"},
        Str.Multi{944, "\u{3A5}\u{308}\u{301}"}
      ],
    [
        Str.Rule{97, 122, 1, 65},
        Str.Rule{181, 181, 1, 924},
        Str.Rule{224, 246, 1, 192},
        Str.Rule{248, 254, 1, 216},
        Str.Rule{255, 255, 1, 376},
        Str.Rule{257, 303, 2, 256},
        Str.Rule{305, 305, 1, 73},
        Str.Rule{307, 311, 2, 306},
        Str.Rule{314, 328, 2, 313},
        Str.Rule{331, 375, 2, 330},
        Str.Rule{378, 382, 2, 377},
        Str.Rule{383, 383, 1, 83},
        Str.Rule{881, 883, 2, 880},
        Str.Rule{887, 887, 1, 886},
        Str.Rule{891, 893, 1, 1021},
        Str.Rule{940, 940, 1, 902},
        Str.Rule{941, 943, 1, 904},
        Str.Rule{945, 961, 1, 913},
        Str.Rule{962, 962, 1, 931},
        Str.Rule{963, 971, 1, 931},
        Str.Rule{972, 972, 1, 908},
        Str.Rule{973, 974, 1, 910},
        Str.Rule{976, 976, 1, 914},
        Str.Rule{977, 977, 1, 920},
        Str.Rule{981, 981, 1, 934},
        Str.Rule{982, 982, 1, 928},
        Str.Rule{983, 983, 1, 975},
        Str.Rule{985, 1007, 2, 984},
        Str.Rule{1008, 1008, 1, 922},
        Str.Rule{1009, 1009, 1, 929},
        Str.Rule{1010, 1010, 1, 1017},
        Str.Rule{1011, 1011, 1, 895},
        Str.Rule{1013, 1013, 1, 917},
        Str.Rule{1016, 1016, 1, 1015},
        Str.Rule{1019, 1019, 1, 1018},
        Str.Rule{1072, 1103, 1, 1040},
        Str.Rule{1104, 1119, 1, 1024},
        Str.Rule{1121, 1153, 2, 1120},
        Str.Rule{1163, 1215, 2, 1162},
        Str.Rule{1218, 1230, 2, 1217},
        Str.Rule{1231, 1231, 1, 1216},
        Str.Rule{1233, 1279, 2, 1232}
      ], x) : String}

# LAW: a code point with a multiple mapping maps to its text
# SYS-CASE-3
law case_multi:
  for ms: List<&2, Str.Multi>
  for rules: List<&2, Str.Rule>
  for +x: U32
  for s: String
  for e: {Str.text.case.multi(ms, x) == Some{s} : Maybe<&2, String>}
  {Str.text.case.of(ms, rules, x) == s : String}

# LAW: any other code point maps to the one code point the rules give
# SYS-CASE-3
law case_rules:
  for ms: List<&2, Str.Multi>
  for rules: List<&2, Str.Rule>
  for +x: U32
  for e: {Str.text.case.multi(ms, x) == None{} : Maybe<&2, String>}
  {Str.text.case.of(ms, rules, x)
    == SCon{Chr{Str.text.case.apply(rules, x)}, SNil{}} : String}

# LAW: no entry holds no multiple mapping
# SYS-CASE-3
law multi_none:
  for x: U32
  {Str.text.case.multi([], x) == None{} : Maybe<&2, String>}

# LAW: the first entry for a code point gives its text
# SYS-CASE-3
law multi_hit:
  for +from: U32
  for to: String
  for rest: List<&2, Str.Multi>
  for +x: U32
  for e: {U32.is_eq(from, x) == True{} : Bool}
  {Str.text.case.multi(Str.Multi{from, to} <> rest, x) == Some{to}
    : Maybe<&2, String>}

# LAW: an entry for another code point is passed over
# SYS-CASE-3
law multi_miss:
  for +from: U32
  for to: String
  for rest: List<&2, Str.Multi>
  for +x: U32
  for e: {U32.is_eq(from, x) == False{} : Bool}
  {Str.text.case.multi(Str.Multi{from, to} <> rest, x)
    == Str.text.case.multi(rest, x) : Maybe<&2, String>}

# LAW: no rule leaves a code point as it is
# SYS-CASE-3
law apply_none:
  for x: U32
  {Str.text.case.apply([], x) == x : U32}

# LAW: the first rule that covers a code point maps it
# SYS-CASE-3
law apply_hit:
  for +r: Str.Rule
  for rest: List<&2, Str.Rule>
  for +x: U32
  for e: {Str.text.case.covers(r, x) == True{} : Bool}
  {Str.text.case.apply(r <> rest, x) == Str.text.case.target(r, x) : U32}

# LAW: a rule that does not cover a code point is passed over
# SYS-CASE-3
law apply_miss:
  for +r: Str.Rule
  for rest: List<&2, Str.Rule>
  for +x: U32
  for e: {Str.text.case.covers(r, x) == False{} : Bool}
  {Str.text.case.apply(r <> rest, x) == Str.text.case.apply(rest, x) : U32}

# LAW: a rule covers the code points from lo to hi, every step-th from lo
# SYS-CASE-3
law covers_def:
  for +lo: U32
  for +hi: U32
  for +step: U32
  for to: U32
  for +x: U32
  {Str.text.case.covers(Str.Rule{lo, hi, step, to}, x)
    == Bool.and(Bool.and(U32.is_ge(x, lo), U32.is_le(x, hi)),
      U32.is_eq(((x - lo) % step : U32), 0)) : Bool}

# LAW: a rule maps lo to `to`, and each code point after it as far on
# SYS-CASE-3
law target_def:
  for +lo: U32
  for hi: U32
  for step: U32
  for +to: U32
  for +x: U32
  {Str.text.case.target(Str.Rule{lo, hi, step, to}, x) == (to + (x - lo) : U32)
    : U32}

# --- width (SYS-WIDTH) ---

# LAW: pad_right writes the text, then a space for every code point it is
# short of n
# SYS-WIDTH-1
law pad_form:
  for +s: String
  for +n: Nat
  {Str.text.pad_right(s, n)
    == s ++ String.repeat(" ", Nat.sub(n, String.length(s))) : String}

# LAW: pad_right is n code points long, or the text's length when it is
# longer
# SYS-WIDTH-1
law pad_length:
  for +s: String
  for +n: Nat
  {String.length(Str.text.pad_right(s, n)) == Nat.max(String.length(s), n)
    : Nat}

# LAW: truncate is the text's first part: the rest after it gives the text
# back
# SYS-WIDTH-2
law trunc_split:
  for +s: String
  for +n: Nat
  {Str.text.truncate(s, n) ++ String.drop(s, n) == s : String}

# LAW: truncate is n code points long, or the text's length when it is
# shorter
# SYS-WIDTH-2
law trunc_length:
  for +s: String
  for +n: Nat
  {String.length(Str.text.truncate(s, n)) == Nat.min(String.length(s), n)
    : Nat}

# --- digit strings (SYS-DIG) ---

# LAW: digits.cmp compares the texts without their leading zeros: the
# shorter is the lesser, and two of one length compare by String.order
# SYS-DIG-1
law dig_rule:
  for a: String
  for b: String
  {Str.text.digits.cmp(a, b) == Str.text.digits.by(
    Nat.cmp(String.length(Str.text.digits.trim(a)),
      String.length(Str.text.digits.trim(b))),
    Str.text.digits.trim(a), Str.text.digits.trim(b)) : Cmp}

# LAW: a shorter text is the lesser
# SYS-DIG-1
law dig_shorter:
  for a: String
  for b: String
  {Str.text.digits.by(LT{}, a, b) == LT{} : Cmp}

# LAW: a longer text is the greater
# SYS-DIG-1
law dig_longer:
  for a: String
  for b: String
  {Str.text.digits.by(GT{}, a, b) == GT{} : Cmp}

# LAW: two texts of one length compare by String.order
# SYS-DIG-1
law dig_same:
  for +a: String
  for +b: String
  {Str.text.digits.by(EQ{}, a, b) == String.order(a, b) : Cmp}

# LAW: a leading '0' is dropped, and trimming goes on
# SYS-DIG-1
law trim_zero:
  for +t: String
  {Str.text.digits.trim(SCon{'0', t}) == Str.text.digits.trim(t) : String}

# LAW: a text that starts with anything but '0' is kept
# SYS-DIG-1
law trim_keep:
  for +h: Char
  for +t: String
  for e: {Char.is_eq(h, '0') == False{} : Bool}
  {Str.text.digits.trim(SCon{h, t}) == SCon{h, t} : String}

# LAW: the empty text trims to itself
# SYS-DIG-1
law trim_empty:
  for s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {Str.text.digits.trim(s) == s : String}
