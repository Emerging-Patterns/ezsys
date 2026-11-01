# For every answer of one read and every text read before it, `file.read`'s
# step stops with that answer's failure unchanged when the read failed; stops
# with exactly the text read before it when the read answered an empty chunk;
# and otherwise reads on with the text read before it followed by the chunk.
#
# `file.read`, `file.write` and `file.save` answer `Result<&1, &1, U32 &
# String, A>`, Base's own shape: a failure is `Fail{(errno, message)}` and is
# a value, never an exit. `file.read` opens the file, asks its size, and reads
# chunks of at least that many bytes (and at least 64 KiB) until a read
# answers an empty chunk.
import Base
import ../src/step.bend as Step

# --- files ---

# LAW: a read that fails stops with its failure unchanged
law read_fail:
  for code: U32
  for why: String
  for got: String
  {Step.read.step(Fail{(code, why)}, got) == Step.ReadStop{Fail{(code, why)}}
    : Step.Read}

# LAW: an empty chunk stops with exactly the text read before it
law read_end:
  for got: String
  {Step.read.step(Done{""}, got) == Step.ReadStop{Done{got}} : Step.Read}

# LAW: any other chunk is appended to the text read before it
law read_more:
  for h: Char
  for t: String
  for got: String
  {Step.read.step(Done{SCon{h, t}}, got) == Step.ReadMore{got ++ SCon{h, t}}
    : Step.Read}
