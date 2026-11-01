# For every second of these days, 53-week and 52-week years end where they
# belong: 2020-12-31 and 2026-12-31 are in week 53 of their year, 2021-12-31
# is 2021-W52, 2025-12-28 is 2025-W52 and 2025-12-29 is 2026-W01.
import Base
import ../src/clock.bend as Clock

# LAW: every second of 2020-12-31 (Thursday) is in week 53 of 2020
law week_53_2020:
  for secs: U32
  for e: {(secs / 86400 : U32) == 18627 : U32}
  {Clock.time.iso_week(secs) == (2020, 53) : U32 & U32}

# LAW: every second of 2026-12-31 (Thursday) is in week 53 of 2026
law week_53_2026:
  for secs: U32
  for e: {(secs / 86400 : U32) == 20818 : U32}
  {Clock.time.iso_week(secs) == (2026, 53) : U32 & U32}

# LAW: every second of 2021-12-31 (Friday) is in week 52 of 2021
law week_52_2021:
  for secs: U32
  for e: {(secs / 86400 : U32) == 18992 : U32}
  {Clock.time.iso_week(secs) == (2021, 52) : U32 & U32}

# LAW: every second of 2025-12-28 (Sunday) is in week 52 of 2025
law week_52_2025:
  for secs: U32
  for e: {(secs / 86400 : U32) == 20450 : U32}
  {Clock.time.iso_week(secs) == (2025, 52) : U32 & U32}

# LAW: every second of 2025-12-29 (Monday) is in week 1 of 2026
law week_after_52_2025:
  for secs: U32
  for e: {(secs / 86400 : U32) == 20451 : U32}
  {Clock.time.iso_week(secs) == (2026, 1) : U32 & U32}
