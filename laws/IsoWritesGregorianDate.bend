# For every day number `d` from 0 to 49710, `time.iso` writes day `d` as the
# proleptic Gregorian date `d` days after 1970-01-01.
#
# pending: no law here yet.
#
# Proved: the date of each day laws/LeapAndCenturyRulesHold.bend and
# laws/InputBoundariesDated.bend name, for every instant of it, and the shape
# and split of laws/IsoHasFixedShape.bend and laws/IsoWritesDayAndClock.bend.
#
# Left to prove: every other day. A proof for every `d` needs lemmas on U32
# division that Base does not have, and a law that walks all 49711 days runs
# out of time in the checker (1000 days took 55 s).
import Base


