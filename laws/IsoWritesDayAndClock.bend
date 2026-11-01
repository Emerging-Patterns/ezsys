# For every `secs` and `ms`, `time.iso(secs, ms)` is the date of day `secs /
# 86400`, then `T`, then two digits each of `secs % 86400 / 3600`, `secs %
# 86400 % 3600 / 60` and `secs % 86400 % 60` joined by `:`, then `.`, three
# digits of `ms` and `Z`; the date is four digits of the year, `-`, two of the
# month, `-`, two of the day. So every instant of one UTC day carries the same
# date.
#
# `time.now()` answers whole seconds since 1970-01-01T00:00:00Z as a `U32`,
# which holds every second up to 2106-02-07T06:28:15Z, and the milliseconds
# past that second. `time.iso(secs, ms)` writes them as ISO 8601 UTC,
# `YYYY-MM-DDTHH:MM:SS.mmmZ`, with the proleptic Gregorian calendar of Howard
# Hinnant's `civil_from_days`; the milliseconds are written as their last
# three decimal places. `time.now_iso()` is `time.iso` of `time.now()`
# (trusted in src/sys.bend). Years before 1970, 1900 among them, are outside
# the input, so the century rule is checked at 2100 instead.
import Base
import ../src/clock.bend as Clock

# LAW: the date is the day's, then T and the time of day
law iso_split:
  for secs: U32
  for ms: U32
  {Clock.time.iso(secs, ms) == Clock.time.date((secs / 86400 : U32))
    ++ "T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: the time of day is hours, minutes and seconds of the second of the
# day, then the milliseconds
law clock_fields:
  for sod: U32
  for ms: U32
  {Clock.time.clock(sod, ms) == Clock.time.two((sod / 3600 : U32)) ++ ":"
    ++ Clock.time.two((sod % 3600 / 60 : U32)) ++ ":"
    ++ Clock.time.two((sod % 60 : U32)) ++ "." ++ Clock.time.three(ms) ++ "Z"
    : String}

# LAW: the date is four digits of the year, two of the month and two of the
# day of the day number
law date_fields:
  for days: U32
  {Clock.time.date(days) == Clock.time.ymd.of(Clock.time.civil(days))
    : String}
