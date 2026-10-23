# ezsys/src/step: every decision the file and environment helpers make. It
# does no IO; src/sys.bend runs the effects and acts on these answers
# (SYS-TRUST-4).
import Base

# after one read: read again with the text so far, or stop with an answer
type Read is Type:
  ReadMore{text: String}
  ReadStop{answer: Result<&1, &1, U32 & String, String>}

# after the temporary file is written: rename it, or stop with a failure
type Save is Type:
  SaveMove{}
  SaveStop{error: U32 & String}

# the bytes one read asks for: the file's size, and at least 64 KiB
def read.chunk(size: U32) -> U32:
  U32.max(size, 65536)

# a chunk that is empty ends the file; any other is appended
def read.more(empty: Bool, text: String, got: String) -> Read:
  match empty:
    case True{}:
      ReadStop{Done{got}}
    case False{}:
      ReadMore{got ++ text}

# what one read's answer means, with the text read before it
def read.step(res: Result<&1, &1, U32 & String, String>, got: String) -> Read:
  match res:
    case Fail{error}:
      ReadStop{Fail{error}}
    case Done{+text}:
      read.more(String.is_empty(text), text, got)

# the answer when a file has not ended after every read file.read makes
def read.spent() -> Result<&1, &1, U32 & String, String>:
  Fail{(27, "ezsys: file.read: the file did not end")}

# where file.save writes before it renames
def save.tmp(path: String) -> String:
  path ++ ".tmp"

# what the temporary file's write answer means
def save.step(res: Result<&1, &1, U32 & String, Unit>) -> Save:
  match res:
    case Fail{error}:
      SaveStop{error}
    case Done{_u}:
      SaveMove{}

# an environment variable's value, or the fallback when it is unset
def env.pick(
  res: Result<&1, &1, U32 & String, String>,
  fallback: String
) -> String:
  match res:
    case Fail{_error}:
      fallback
    case Done{value}:
      value
