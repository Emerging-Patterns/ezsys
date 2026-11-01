# For every `secs` and `ms`, `time.iso(secs, ms)` is exactly
# `time.civil(secs)`'s year in four digits, `-`, month, `-`, day, `T`, hour,
# `:`, minute, `:`, second (two digits each), `.`, three digits of `ms` and
# `Z`: the civil fields are the ones `time.iso` writes.
#
# `time.civil(secs)` answers the civil fields of an instant in UTC as `(year,
# month, day, hour, minute, second, weekday)`, with the date and time
# `time.iso` writes and the ISO 8601 weekday, 1 for Monday to 7 for Sunday
# (ISO 8601-1:2019 §3.2.2 and §4.3.2.2, Python's `isoweekday()`).
import Base
import ../src/clock.bend as Clock

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

# LAW: the civil fields are the ones time.iso writes
law civil_iso:
  for +secs: U32
  for +ms: U32
  {Clock.time.iso(secs, ms) == civil_text(Clock.time.fields(secs), ms)
    : String}
