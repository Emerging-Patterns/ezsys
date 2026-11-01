# For every `secs` in the day and every `ms`, the boundaries of the input and
# of a millennium fall where they belong: day 0 is 1970-01-01, day 10956 is
# 1999-12-31, day 10957 is 2000-01-01, and day 49710 is 2106-02-07; and for
# every `ms`, the last second, 4294967295, is `2106-02-07T06:28:15`.
import Base
import ../src/clock.bend as Clock

# LAW: day 0 is 1970-01-01, at every second of it
law epoch:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 0 : U32}
  {Clock.time.iso(secs, ms)
    == "1970-01-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 10956 is 1999-12-31, at every second of it
law eve_2000:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 10956 : U32}
  {Clock.time.iso(secs, ms)
    == "1999-12-31T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 10957 is 2000-01-01, at every second of it
law day_2000:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 10957 : U32}
  {Clock.time.iso(secs, ms)
    == "2000-01-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 49710 is 2106-02-07, at every second of it
law last_day:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 49710 : U32}
  {Clock.time.iso(secs, ms)
    == "2106-02-07T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: the last second a U32 holds is 2106-02-07T06:28:15
law last_second:
  for ms: U32
  {Clock.time.iso(4294967295, ms)
    == "2106-02-07T06:28:15." ++ Clock.time.three(ms) ++ "Z" : String}
