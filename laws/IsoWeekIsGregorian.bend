# For every day number `d` from 0 to 49710, `time.iso_week` answers the ISO
# 8601 week-numbering year and week of the proleptic Gregorian date `d` days
# after 1970-01-01.
#
# pending: no law here yet.
#
# Proved: the ISO year and week of each day laws/IsoWeekYearBoundaries.bend
# and laws/IsoWeekYearLengths.bend name, for every instant of it, and the rule
# of laws/IsoWeekOfThursday.bend for every day.
#
# Left to prove: every other day. It rests on
# laws/IsoWritesGregorianDate.bend's date of the week's Thursday and on
# `time.jan1` for every year, which need the same U32 division lemmas. The
# differential test against Python's `isocalendar()` and `date -u +%G-W%V`
# agrees on every case it ran.
import Base


