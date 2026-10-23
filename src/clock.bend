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
