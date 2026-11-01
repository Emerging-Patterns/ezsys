# For every second of these days, the year boundary falls as ISO 8601 has it:
# 2008-12-29 is 2009-W01, 2014-12-31 is 2015-W01, 2019-12-30 is 2020-W01 and
# 2024-12-31 is 2025-W01 (29 to 31 December in week 1 of the next year);
# 2010-01-03 is 2009-W53, 2016-01-01 is 2015-W53, 2021-01-03 is 2020-W53,
# 2022-01-01 is 2021-W52, 2023-01-01 is 2022-W52 and 2027-01-01 is 2026-W53 (1
# to 3 January in the last week of the year before).
import Base
import ../src/clock.bend as Clock

# LAW: every second of 2008-12-29 is written 2009-W01, the week zero-padded
law week_text_2009:
  for secs: U32
  for e: {(secs / 86400 : U32) == 14242 : U32}
  {Clock.time.iso_week_text(secs) == "2009-W01" : String}

# LAW: every second of 2008-12-29 (Monday) is in week 1 of 2009
law week_dec29_2008:
  for secs: U32
  for e: {(secs / 86400 : U32) == 14242 : U32}
  {Clock.time.iso_week(secs) == (2009, 1) : U32 & U32}

# LAW: every second of 2014-12-31 (Wednesday) is in week 1 of 2015
law week_dec31_2014:
  for secs: U32
  for e: {(secs / 86400 : U32) == 16435 : U32}
  {Clock.time.iso_week(secs) == (2015, 1) : U32 & U32}

# LAW: every second of 2019-12-30 (Monday) is in week 1 of 2020
law week_dec30_2019:
  for secs: U32
  for e: {(secs / 86400 : U32) == 18260 : U32}
  {Clock.time.iso_week(secs) == (2020, 1) : U32 & U32}

# LAW: every second of 2024-12-31 (Tuesday) is in week 1 of 2025
law week_dec31_2024:
  for secs: U32
  for e: {(secs / 86400 : U32) == 20088 : U32}
  {Clock.time.iso_week(secs) == (2025, 1) : U32 & U32}

# LAW: every second of 2010-01-03 (Sunday) is in week 53 of 2009
law week_jan3_2010:
  for secs: U32
  for e: {(secs / 86400 : U32) == 14612 : U32}
  {Clock.time.iso_week(secs) == (2009, 53) : U32 & U32}

# LAW: every second of 2016-01-01 (Friday) is in week 53 of 2015
law week_jan1_2016:
  for secs: U32
  for e: {(secs / 86400 : U32) == 16801 : U32}
  {Clock.time.iso_week(secs) == (2015, 53) : U32 & U32}

# LAW: every second of 2021-01-03 (Sunday) is in week 53 of 2020
law week_jan3_2021:
  for secs: U32
  for e: {(secs / 86400 : U32) == 18630 : U32}
  {Clock.time.iso_week(secs) == (2020, 53) : U32 & U32}

# LAW: every second of 2022-01-01 (Saturday) is in week 52 of 2021
law week_jan1_2022:
  for secs: U32
  for e: {(secs / 86400 : U32) == 18993 : U32}
  {Clock.time.iso_week(secs) == (2021, 52) : U32 & U32}

# LAW: every second of 2023-01-01 (Sunday) is in week 52 of 2022
law week_jan1_2023:
  for secs: U32
  for e: {(secs / 86400 : U32) == 19358 : U32}
  {Clock.time.iso_week(secs) == (2022, 52) : U32 & U32}

# LAW: every second of 2027-01-01 (Friday) is in week 53 of 2026
law week_jan1_2027:
  for secs: U32
  for e: {(secs / 86400 : U32) == 20819 : U32}
  {Clock.time.iso_week(secs) == (2026, 53) : U32 & U32}
