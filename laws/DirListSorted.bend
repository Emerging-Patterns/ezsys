# For every list of raw names, every name in `dir.list`'s step's answer is no
# greater by `String.order` than the name after it.
import Base
import ../src/dir.bend as Dir

# whether every name after prev is no greater than the one before it
def ascending.from(xs: List<&2, String>, +prev: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(String.is_le(prev, y), ascending.from(rest, y))

# whether every name is no greater by String.order than the one after it
def ascending(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      ascending.from(rest, x)

# LAW: the answer is ascending by String.order
law dir_sorted:
  for raw: List<&2, String>
  {ascending(Dir.dir.names(raw)) == True{} : Bool}
