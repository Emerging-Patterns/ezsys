# For every path, `file.save` writes its text to exactly `path ++ ".tmp"`;
# when that write fails it answers the failure unchanged and renames nothing,
# and when it succeeds it renames exactly `path ++ ".tmp"` to exactly `path`
# and answers the rename's result.
import Base
import ../src/step.bend as Step

# LAW: file.save writes to the path with .tmp after it
law save_tmp:
  for path: String
  {Step.save.tmp(path) == path ++ ".tmp" : String}

# LAW: a failed write of the temporary file is the answer, and nothing is
# renamed
law save_fail:
  for code: U32
  for why: String
  {Step.save.step(Fail{(code, why)}) == Step.SaveStop{(code, why)} : Step.Save}

# LAW: a written temporary file is renamed
law save_move:
  for u: Unit
  {Step.save.step(Done{u}) == Step.SaveMove{} : Step.Save}
