# For every two strings `a` and `b` of ASCII digits, `text.digits.cmp(a, b)`
# is the order of their values as natural numbers.
#
# pending: no law here yet.
#
# Proved: nothing by a law. The rule of laws/DigitsCmpTrimsThenCompares.bend
# is proved, and the differential test against Python's `int` agrees on every
# case it ran.
#
# Left to prove: a law over a digit string's value: past its leading zeros a
# text of `k` digits has a value from `10^(k-1)` to `10^k - 1`, and two of one
# length compare as their first differing digits do. That needs lemmas Base
# does not have: on `Nat` sums and products against `Nat.cmp`, and that
# `U32.cmp` of two code points is `Nat.cmp` of their values.
import Base


