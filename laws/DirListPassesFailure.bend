# For every answer of the directory read, `dir.list`'s step answers a failure
# unchanged, and the sorted names of laws/DirListKeepsEveryName.bend and
# laws/DirListSorted.bend when the read succeeded.
import Base
import ../src/dir.bend as Dir

# LAW: a failed directory read is the answer unchanged
law dir_fail:
  for code: U32
  for why: String
  {Dir.dir.step(Fail{(code, why)}) == Fail{(code, why)}
    : Result<&1, &1, U32 & String, List<&2, String>>}

# LAW: a directory read's names are answered as dir.names gives them
law dir_done:
  for raw: List<&2, String>
  {Dir.dir.step(Done{raw}) == Done{Dir.dir.names(raw)}
    : Result<&1, &1, U32 & String, List<&2, String>>}
