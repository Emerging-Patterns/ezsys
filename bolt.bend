# bolt.bend: how bolt lints this repo. Every rule is an error except
# `coverage`: the gate must see no errors. See bolt/config.bend for the groups
# and levels.
import Base

# what will fail or blow up
def correctness() -> String:
  "error"

# what is probably a slip
def suspicious() -> String:
  "error"

# comments and whitespace
def style() -> String:
  "error"

# a pure def named by no quantified law
def laws() -> String:
  "error"

# a def no quantified law reaches: warn, as in ezhttp, because bolt does not
# count ENTRY.bend's fills (they fill laws stated in the same file) and the
# example program under examples/ is no law's subject
def coverage() -> String:
  "warn"

# a law with no binder
def closed() -> String:
  "error"

# an @unsafe def a law file reaches
def unsafe() -> String:
  "error"

# SPEC.md's rows and the laws' tags agree
def trace() -> String:
  "error"
