# For every `secs`, `time.iso_week(secs)` is the calendar year of the Thursday
# of its day's week (the day plus 4 less its weekday) and one more than the
# whole weeks from that year's 1 January to that Thursday;
# `time.iso_week_text` writes the year in four digits, `-W` and the week in
# two.
#
# `time.iso_week(secs)` answers the ISO 8601 week date's year and week (ISO
# 8601-1:2019 §3.2.2 and §5.2.4.3, Python's `date.isocalendar()`, `date`'s
# `%G` and `%V`): a week runs Monday to Sunday, and week 1 of a year is the
# week that holds its first Thursday, so a day belongs to the ISO year and
# week of its week's Thursday, and the ISO year of 29 to 31 December or 1 to 3
# January can be the next or the previous calendar year. A year has 53 weeks
# when it starts on a Thursday, or is a leap year that starts on a Wednesday
# (2015, 2020, 2026), and 52 otherwise. `time.iso_week_text(secs)` writes them
# as `date -u +%G-W%V` does, `YYYY-Www` with the week in two digits, as in
# `2026-W43`. 1 January's day number is Howard Hinnant's `days_from_civil`.
# The zero-padded week is checked at 2008-12-29, 2009-W01, in
# laws/IsoWeekYearBoundaries.bend.
import Base
import ../src/clock.bend as Clock

# LAW: a day's ISO year and week are its week's Thursday's calendar year and
# how many Thursdays of that year it is
law week_rule:
  for +secs: U32
  {Clock.time.iso_week(secs)
    == Clock.time.week.of(Clock.time.thursday((secs / 86400 : U32)),
      Clock.time.civil(Clock.time.thursday((secs / 86400 : U32))))
    : U32 & U32}

# LAW: a week's Thursday is 4 less the weekday days on, Monday to Sunday
law thursday_def:
  for +days: U32
  {Clock.time.thursday(days) == (days + 4 - Clock.time.weekday(days) : U32)
    : U32}

# LAW: the week of a Thursday is one more than the whole weeks since 1
# January of its year
law week_of_def:
  for +thu: U32
  for +year: U32
  for month: U32
  for day: U32
  {Clock.time.week.of(thu, Clock.Ymd{year, month, day})
    == (year, ((thu - Clock.time.jan1(year)) / 7 + 1 : U32)) : U32 & U32}

# LAW: the text of a year and week is YYYY-Www, the week in two digits
law week_text:
  for year: U32
  for num: U32
  {Clock.time.week.text((year, num))
    == Clock.time.four(year) ++ "-W" ++ Clock.time.two(num) : String}

# LAW: iso_week_text writes iso_week
law week_text_of:
  for +secs: U32
  {Clock.time.iso_week_text(secs)
    == Clock.time.week.text(Clock.time.iso_week(secs)) : String}
