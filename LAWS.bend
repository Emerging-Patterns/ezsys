# ezsys's laws. Each guarantee is one file under laws/, its prose on top and
# its quantified laws under it, proved by the file of the same name under
# proofs/; LAWS.bend and PROOF.bend only import them. A law file that says
# pending proves part of its guarantee, not all of it; one with no law yet is
# not imported. The gate: the first line `bend PROOF.bend` prints is exactly
# `ALL PROOFS CHECK`. Tests and fixtures are never evidence for a guarantee;
# what ezsys cannot prove is said where it is assumed, on the code.
#
# Every guarantee is about the public interface in main.bend. Its pure
# functions are thin names for the functions in src/text.bend, src/str.bend,
# src/clock.bend and src/errno.bend, which the laws are stated for (a name in
# main.bend is that function and no more, so it carries no law of its own; it
# is dotted, which bolt's `coverage` rule reads as a helper), and every
# decision its IO functions make is a function in src/step.bend or
# src/dir.bend. Those modules do no IO, so the law and proof files import them
# and nothing else. src/sys.bend runs the effects and acts on the answers
# (trusted in src/sys.bend). It is the only module with foreign code: one
# effect that flushes and renames a file, one that reads the wall clock and
# one that reads a directory's names, each trusted where src/sys.bend declares
# it.
#
# In the template guarantees (laws/Fill*.bend), `O` and `C` are any nonempty
# open and close delimiters. In the replace and split guarantees, `O` is any
# nonempty text.
#
# docs/SPEC.md is the requirement table these files replaced, kept as a
# record; it names the guarantees by requirement IDs.
import Base
import ./laws/CaseFollowsTables.bend as CaseFollowsTables
import ./laws/CaseMapsEachChar.bend as CaseMapsEachChar
import ./laws/CaseTableLookup.bend as CaseTableLookup
import ./laws/CivilFieldsMatchIso.bend as CivilFieldsMatchIso
import ./laws/DigitsCmpTrimsThenCompares.bend as DigitsCmpTrimsThenCompares
import ./laws/DirListKeepsEveryName.bend as DirListKeepsEveryName
import ./laws/DirListPassesFailure.bend as DirListPassesFailure
import ./laws/DirListSorted.bend as DirListSorted
import ./laws/EnvOrFallsBack.bend as EnvOrFallsBack
import ./laws/ErrOsWritesPythonText.bend as ErrOsWritesPythonText
import ./laws/FillCopiesPlain.bend as FillCopiesPlain
import ./laws/FillKeepsUnclosedMarker.bend as FillKeepsUnclosedMarker
import ./laws/FillKeepsUnknownKey.bend as FillKeepsUnknownKey
import ./laws/FillLeavesUnmarked.bend as FillLeavesUnmarked
import ./laws/FillUsesBraces.bend as FillUsesBraces
import ./laws/FillWritesKnownKey.bend as FillWritesKnownKey
import ./laws/FindAgreesWithContains.bend as FindAgreesWithContains
import ./laws/FindGivesFirstIndex.bend as FindGivesFirstIndex
import ./laws/FirstPairGivesValue.bend as FirstPairGivesValue
import ./laws/InputBoundariesDated.bend as InputBoundariesDated
import ./laws/IsoHasFixedShape.bend as IsoHasFixedShape
import ./laws/IsoWeekOfThursday.bend as IsoWeekOfThursday
import ./laws/IsoWeekYearBoundaries.bend as IsoWeekYearBoundaries
import ./laws/IsoWeekYearLengths.bend as IsoWeekYearLengths
import ./laws/IsoWritesDayAndClock.bend as IsoWritesDayAndClock
import ./laws/LeapAndCenturyRulesHold.bend as LeapAndCenturyRulesHold
import ./laws/LstripDropsLeadingSpace.bend as LstripDropsLeadingSpace
import ./laws/PadRightFillsSpaces.bend as PadRightFillsSpaces
import ./laws/ReadStepAccumulates.bend as ReadStepAccumulates
import ./laws/ReplaceEmptyFillsGaps.bend as ReplaceEmptyFillsGaps
import ./laws/ReplaceScansLeftToRight.bend as ReplaceScansLeftToRight
import ./laws/ReprQuotesAndEscapes.bend as ReprQuotesAndEscapes
import ./laws/RstripDropsTrailingSpace.bend as RstripDropsTrailingSpace
import ./laws/SaveWritesTmpThenRenames.bend as SaveWritesTmpThenRenames
import ./laws/SpaceIsPythonWhitespace.bend as SpaceIsPythonWhitespace
import ./laws/SplitKeepsEmptyPieces.bend as SplitKeepsEmptyPieces
import ./laws/StrerrorTableLookup.bend as StrerrorTableLookup
import ./laws/TruncateTakesPrefix.bend as TruncateTakesPrefix
import ./laws/WeekdayCountsFromThursday.bend as WeekdayCountsFromThursday
