# ezsys/src/clock: Unix time as ISO 8601 UTC, `YYYY-MM-DDTHH:MM:SS.mmmZ`.
# Pure: the wall clock itself is the effect in src/sys.bend. The input is
# whole seconds since 1970-01-01T00:00:00Z as a U32, which reaches
# 2106-02-07T06:28:15Z, and the milliseconds past that second.
#
# The date is Howard Hinnant's civil_from_days
# (https://howardhinnant.github.io/date_algorithms.html#civil_from_days), the
# proleptic Gregorian calendar in 400-year eras of 146097 days, its years
# starting on 1 March so that the leap day is the last day of a year. Every
# intermediate value is unsigned and fits in a U32 for every U32 input.
import Base

# a calendar date
type Ymd is Data:
  Ymd{year: U32, month: U32, day: U32}

# the k-th decimal digit character (9 for anything past it)
def time.digit.at(place: Nat) -> Char:
  match place:
    case 0n:
      '0'
    case 1n+k1:
      match k1:
        case 0n:
          '1'
        case 1n+k2:
          match k2:
            case 0n:
              '2'
            case 1n+k3:
              match k3:
                case 0n:
                  '3'
                case 1n+k4:
                  match k4:
                    case 0n:
                      '4'
                    case 1n+k5:
                      match k5:
                        case 0n:
                          '5'
                        case 1n+k6:
                          match k6:
                            case 0n:
                              '6'
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  '7'
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      '8'
                                    case 1n+_k9:
                                      '9'

# the decimal digit of n's last place
def time.digit(num: U32) -> Char:
  time.digit.at(U32.to_nat((num % 10 : U32)))

# the month of a March-based month index (0 is March)
def time.civil.month(+mp: U32) -> U32:
  Bool.pick(U32, (mp < 10 : U32), (mp + 3 : U32), (mp - 9 : U32))

# the calendar year of a March-based year: January and February are the
# next calendar year's
def time.civil.year(+year: U32, +month: U32) -> U32:
  Bool.pick(U32, (month <= 2 : U32), (year + 1 : U32), year)

# the year, month and day of a day number (days since 1970-01-01)
def time.civil(days: U32) -> Ymd:
  +z = (days + 719468 : U32)
  +era = (z / 146097 : U32)
  +doe = (z - era * 146097 : U32)
  +yoe = ((doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 : U32)
  +doy = (doe - (365 * yoe + yoe / 4 - yoe / 100) : U32)
  +mp = ((5 * doy + 2) / 153 : U32)
  +m = time.civil.month(mp)
  Ymd{time.civil.year((yoe + era * 400 : U32), m), m,
    (doy - (153 * mp + 2) / 5 + 1 : U32)}

# two decimal places: tens and units
def time.two(+num: U32) -> String:
  SCon{time.digit((num / 10 : U32)), SCon{time.digit(num), SNil{}}}

# three decimal places: hundreds, tens and units
def time.three(+num: U32) -> String:
  SCon{time.digit((num / 100 : U32)), SCon{time.digit((num / 10 : U32)),
    SCon{time.digit(num), SNil{}}}}

# four decimal places: thousands, hundreds, tens and units
def time.four(+num: U32) -> String:
  SCon{time.digit((num / 1000 : U32)), SCon{time.digit((num / 100 : U32)),
    SCon{time.digit((num / 10 : U32)), SCon{time.digit(num), SNil{}}}}}

# YYYY-MM-DD
def time.ymd(year: U32, month: U32, day: U32) -> String:
  time.four(year) ++ SCon{'-', time.two(month) ++ SCon{'-', time.two(day)}}

# the date of a calendar date
def time.ymd.of(date: Ymd) -> String:
  match date:
    case Ymd{year, month, day}:
      time.ymd(year, month, day)

# YYYY-MM-DD of a day number
def time.date(days: U32) -> String:
  time.ymd.of(time.civil(days))

# HH:MM:SS.mmmZ of a second of the day and a millisecond (its last three
# decimal places)
def time.clock(+sod: U32, ms: U32) -> String:
  time.two((sod / 3600 : U32)) ++ SCon{':', time.two((sod % 3600 / 60 : U32))
    ++ SCon{':', time.two((sod % 60 : U32)) ++ SCon{'.',
    time.three(ms) ++ SCon{'Z', SNil{}}}}}

# ISO 8601 UTC of seconds since the epoch and a millisecond
def time.iso(+secs: U32, ms: U32) -> String:
  time.date((secs / 86400 : U32)) ++ SCon{'T',
    time.clock((secs % 86400 : U32), ms)}

# ISO 8601 UTC of a clock reading: seconds and milliseconds
def time.iso.of(now: U32 & U32) -> String:
  (secs, ms) = now
  time.iso(secs, ms)

# --- weekdays and ISO 8601 weeks ---

# the ISO 8601 weekday after `wd`: 1 is Monday and 7 is Sunday, so Sunday
# is followed by Monday
def time.wd.next(+wd: U32) -> U32:
  Bool.pick(U32, U32.is_eq(wd, 7), 1, (wd + 1 : U32))

# the weekday `left` days after a day whose weekday is `wd`
def time.wd.go(left: Nat, wd: U32) -> U32:
  match left:
    case 0n:
      wd
    case 1n+more:
      time.wd.go(more, time.wd.next(wd))

# the ISO weekday of day `num` after 1970-01-01, a Thursday (4)
def time.weekday.nat(num: Nat) -> U32:
  time.wd.go(num, 4)

# the ISO weekday of a day number
def time.weekday(days: U32) -> U32:
  time.weekday.nat(U32.to_nat(days))

# the day number of 1 January of a year from 1970 on: Howard Hinnant's
# days_from_civil for month 1, day 1
def time.jan1(year: U32) -> U32:
  +yr = (year - 1 : U32)
  +era = (yr / 400 : U32)
  +yoe = (yr - era * 400 : U32)
  (era * 146097 + yoe * 365 + yoe / 4 - yoe / 100 + 306 - 719468 : U32)

# the Thursday of a day's ISO week (Monday to Sunday)
def time.thursday(+days: U32) -> U32:
  (days + 4 - time.weekday(days) : U32)

# the ISO year and week of a week's Thursday: the Thursday's calendar year,
# and how many Thursdays of that year it is
def time.week.of(+thu: U32, date: Ymd) -> U32 & U32:
  match date:
    case Ymd{+year, _month, _day}:
      (year, ((thu - time.jan1(year)) / 7 + 1 : U32))

# the ISO 8601 week-numbering year and week of a day number
def time.week(+days: U32) -> U32 & U32:
  +thu = time.thursday(days)
  time.week.of(thu, time.civil(thu))

# the ISO 8601 week-numbering year and week of seconds since the epoch
def time.iso_week(+secs: U32) -> U32 & U32:
  time.week((secs / 86400 : U32))

# YYYY-Www of an ISO year and week, as `date +%G-W%V` writes it
def time.week.text(week: U32 & U32) -> String:
  (year, num) = week
  time.four(year) ++ SCon{'-', SCon{'W', time.two(num)}}

# YYYY-Www of seconds since the epoch
def time.iso_week_text(+secs: U32) -> String:
  time.week.text(time.iso_week(secs))

# a date, a second of the day and a weekday as the civil fields
def time.fields.of(
  date: Ymd,
  +sod: U32,
  wd: U32
) -> U32 & U32 & U32 & U32 & U32 & U32 & U32:
  match date:
    case Ymd{year, month, day}:
      (year, month, day, (sod / 3600 : U32), (sod % 3600 / 60 : U32),
        (sod % 60 : U32), wd)

# year, month, day, hour, minute, second and ISO weekday of seconds since
# the epoch, in UTC
def time.fields(+secs: U32) -> U32 & U32 & U32 & U32 & U32 & U32 & U32:
  time.fields.of(time.civil((secs / 86400 : U32)), (secs % 86400 : U32),
    time.weekday((secs / 86400 : U32)))
