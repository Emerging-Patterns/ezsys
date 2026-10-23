# ezsys/src/dir: every decision dir.list makes. It does no IO; src/sys.bend
# reads a directory's raw entry names with its own effect (SYS-TRUST-5) and
# hands them here. The answer drops exactly "." and ".." and sorts the rest
# ascending by String.order, which compares code points one by one: that is
# the bytewise order of their UTF-8 encodings.
import Base

# whether a name is "." or ".."
def dir.dot(+name: String) -> Bool:
  Bool.or(String.eq(name, "."), String.eq(name, ".."))

# name before next when it sorts first, else next and the rest with name put
# in them
def dir.insert.pick(
  first: Bool,
  +name: String,
  +next: String,
  +ys: List<&2, String>,
  rest: Unit -> List<&2, String>
) -> List<&2, String>:
  match first:
    case True{}:
      Con{name, Con{next, ys}}
    case False{}:
      Con{next, rest(Unit{})}

# a name put into a sorted list, before the first name it does not sort after
def dir.insert(+name: String, xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      [name]
    case Con{+next, +ys}:
      dir.insert.pick(String.is_le(name, next), name, next, ys,
        _u => dir.insert(name, ys))

# a list sorted ascending by String.order (insertion sort)
def dir.sort(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+name, xt}:
      dir.insert(name, dir.sort(xt))

# a name kept unless it is "." or ".."
def dir.keep.pick(
  dot: Bool,
  +name: String,
  rest: Unit -> List<&2, String>
) -> List<&2, String>:
  match dot:
    case True{}:
      rest(Unit{})
    case False{}:
      Con{name, rest(Unit{})}

# the names that are not "." or "..", in their order
def dir.keep(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+name, xt}:
      dir.keep.pick(dir.dot(name), name, _u => dir.keep(xt))

# what dir.list answers for the raw names a directory read gave
def dir.names(raw: List<&2, String>) -> List<&2, String>:
  dir.sort(dir.keep(raw))

# what dir.list answers for a directory read's answer: its names, or the
# failure unchanged
def dir.step(
  res: Result<&1, &1, U32 & String, List<&2, String>>
) -> Result<&1, &1, U32 & String, List<&2, String>>:
  match res:
    case Fail{error}:
      Fail{error}
    case Done{raw}:
      Done{dir.names(raw)}
