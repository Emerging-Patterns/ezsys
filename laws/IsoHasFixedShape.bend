# For every `secs` and `ms`, `time.iso(secs, ms)` is exactly 24 characters, of
# the form `####-##-##T##:##:##.###Z` where each `#` is an ASCII digit `0` to
# `9`.
import Base
import ../src/clock.bend as Clock

# --- the specification's own words ---

# an ASCII digit becomes '#', any other character stays
def shape.char(chr: Char) -> Char:
  match chr:
    case Chr{+x}:
      Bool.pick(Char, Bool.and((x >= 48 : U32), (x <= 57 : U32)), '#', Chr{x})

# a text with every ASCII digit made '#'
def shape(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{hd, tl}:
      SCon{shape.char(hd), shape(tl)}

# the form of every time.iso
def shape.iso() -> String:
  "####-##-##T##:##:##.###Z"

# --- wall clock ---

# LAW: every time.iso has the form ####-##-##T##:##:##.###Z, # a digit
law iso_shape:
  for +secs: U32
  for +ms: U32
  {shape(Clock.time.iso(secs, ms)) == shape.iso() : String}

# LAW: every time.iso is 24 characters
law iso_width:
  for secs: U32
  for ms: U32
  {String.length(Clock.time.iso(secs, ms)) == 24n : Nat}
