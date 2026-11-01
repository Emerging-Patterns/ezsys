# The weekday of every second of 1970-01-01 is 4 (Thursday); for every `n`,
# the day of the week of day `n + 1` is the one after day `n`'s, and its
# number is the one after, where 7 (Sunday) is followed by 1 (Monday) and any
# other by the next number; for every day number `d`, `time.weekday(d)`,
# computed a bit at a time, is the weekday of the day `d` days after
# 1970-01-01, counted a day at a time; `time.civil`'s weekday is that of `secs
# / 86400`.
#
# The weekday's definition counts from day 0, a Thursday, one day at a time;
# `time.weekday` computes the same day in 32 steps, one for each bit of the
# day number, and the laws here prove the two agree for every day number
# (where a remainder by 7 of a U32 would need lemmas Base does not have).
import Base
import ../src/clock.bend as Clock

# --- weekdays and ISO 8601 weeks ---

# the weekday of the civil fields
def wday(fields: U32 & U32 & U32 & U32 & U32 & U32 & U32) -> U32:
  (_y, _mo, _d, _h, _mi, _s, wd) = fields
  wd

# LAW: every second of 1970-01-01 is a Thursday, ISO weekday 4
law weekday_epoch:
  for secs: U32
  for e: {(secs / 86400 : U32) == 0 : U32}
  {Clock.time.weekday((secs / 86400 : U32)) == 4 : U32}

# LAW: each day's day of the week is the one after the day before's
law weekday_step:
  for num: Nat
  {Clock.time.wd.go(1n+num, Clock.Thu{})
    == Clock.time.wd.next(Clock.time.wd.go(num, Clock.Thu{})) : Clock.Wd}

# LAW: the weekday number after 7 (Sunday) is 1 (Monday); after any other,
# the next number
law weekday_next:
  for day: Clock.Wd
  {Clock.time.wd.num(Clock.time.wd.next(day))
    == Bool.pick(U32, U32.is_eq(Clock.time.wd.num(day), 7), 1,
      (Clock.time.wd.num(day) + 1 : U32)) : U32}

# LAW: the weekday of day n is the number of the day of the week n days
# after 1970-01-01, a Thursday
law weekday_nat:
  for num: Nat
  {Clock.time.weekday.nat(num)
    == Clock.time.wd.num(Clock.time.wd.go(num, Clock.Thu{})) : U32}

# LAW: a day number's weekday, computed a bit at a time, is that of the day
# that many days after 1970-01-01, counted a day at a time
law weekday_days:
  for days: U32
  {Clock.time.weekday(days) == Clock.time.weekday.nat(U32.to_nat(days)) : U32}

# LAW: time.civil's weekday is its day's
law fields_weekday:
  for +secs: U32
  {wday(Clock.time.fields(secs)) == Clock.time.weekday((secs / 86400 : U32))
    : U32}
