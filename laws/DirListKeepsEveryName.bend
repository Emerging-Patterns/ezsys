# For every list of raw names and every name, `dir.list`'s step answers the
# name exactly as many times as the raw names hold it when it is neither `.`
# nor `..`, and never when it is `.` or `..`: no name is lost, added or
# repeated.
#
# `dir.list(path)` answers `Result<&1, &1, U32 & String, List<&2, String>>`:
# the names of the entries in a directory (names only, not paths), or Base's
# `Fail{(errno, message)}`, a value and never an exit. The effect `ezsys.list`
# reads the names as the host lists them (trusted in src/sys.bend), and
# src/dir.bend's step decides the answer: it drops exactly `.` and `..` and
# sorts the rest ascending by Base's `String.order`, which compares code point
# by code point and puts a proper prefix first. That is the bytewise order of
# the names' UTF-8 encodings, since UTF-8 keeps code point order, so for names
# that are valid UTF-8 the answer is Python's `sorted(os.listdir(path))`. A
# name's copies are counted with `listed`, below; laws/DirListSorted.bend
# checks the order with `ascending`.
import Base
import ../src/dir.bend as Dir

# --- directories ---

# one copy of the name, when hit holds
def listed.pick(hit: Bool, count: Nat) -> Nat:
  match hit:
    case True{}:
      1n+count
    case False{}:
      count

# how many times a list holds a name
def listed(+name: String, xs: List<&2, String>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      listed.pick(String.eq(x, name), listed(name, rest))

# LAW: a name that is neither . nor .. is answered as many times as the raw
# names hold it, and . and .. never
law dir_count:
  for +raw: List<&2, String>
  for +name: String
  {listed(name, Dir.dir.names(raw))
    == Bool.pick(Nat, Bool.or(String.eq(name, "."), String.eq(name, "..")),
      0n, listed(name, raw)) : Nat}
