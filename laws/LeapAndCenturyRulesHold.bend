# For every `secs` in the day and every `ms`, the leap and century rules hold
# at these days: day 11016 is 2000-02-29 and day 11017 is 2000-03-01 (2000 is
# divisible by 400), day 19782 is 2024-02-29 and day 19783 is 2024-03-01
# (divisible by 4), day 19416 is 2023-02-28 and day 19417 is 2023-03-01 (not
# divisible by 4), and day 47540 is 2100-02-28 and day 47541 is 2100-03-01
# (divisible by 100, not by 400).
import Base
import ../src/clock.bend as Clock

# LAW: day 11016 is 2000-02-29, at every second of it
law leap_2000:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 11016 : U32}
  {Clock.time.iso(secs, ms)
    == "2000-02-29T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 11017 is 2000-03-01, at every second of it
law leap_2000_after:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 11017 : U32}
  {Clock.time.iso(secs, ms)
    == "2000-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 19782 is 2024-02-29, at every second of it
law leap_2024:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 19782 : U32}
  {Clock.time.iso(secs, ms)
    == "2024-02-29T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 19783 is 2024-03-01, at every second of it
law leap_2024_after:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 19783 : U32}
  {Clock.time.iso(secs, ms)
    == "2024-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 19416 is 2023-02-28, at every second of it
law common_2023:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 19416 : U32}
  {Clock.time.iso(secs, ms)
    == "2023-02-28T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 19417 is 2023-03-01, at every second of it
law common_2023_after:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 19417 : U32}
  {Clock.time.iso(secs, ms)
    == "2023-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 47540 is 2100-02-28, at every second of it
law century_2100:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 47540 : U32}
  {Clock.time.iso(secs, ms)
    == "2100-02-28T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 47541 is 2100-03-01, at every second of it
law century_2100_after:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 47541 : U32}
  {Clock.time.iso(secs, ms)
    == "2100-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
