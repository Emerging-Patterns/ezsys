# ezsys/src/sys: the effects. Every decision these make is src/step.bend's or
# src/clock.bend's; this module runs the effects in order and acts on the
# answers (SYS-TRUST-4). The two effects of its own are foreign code, a C
# file and its JS twin each: a flush-and-rename (SYS-TRUST-1) and the wall
# clock (SYS-TRUST-2).
import Base
import ./step.bend as Step
import ./clock.bend as Clock

# flush `from` to disk, then rename it over `to`
def ezsys.rename(
  from: String,
  to: String
) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "./effs/rename.c"
  import "./effs/rename.js"

# whole seconds since 1970-01-01T00:00:00Z and the milliseconds past them
def ezsys.clock() -> IO(U32 & U32):
  import "./effs/clock.c"
  import "./effs/clock.js"

# reads one file.read makes at most
def sys.read.fuel() -> Nat:
  65536n

# close the file, then answer
def sys.read.end(
  file: File,
  answer: Result<&1, &1, U32 & String, String>
) -> IO(Result<&1, &1, U32 & String, String>):
  IO.bind(Unit, Result<&1, &1, U32 & String, String>, File.close(file),
    _u => IO.pure(Result<&1, &1, U32 & String, String>, answer))

# act on one read's step: read on, or close and answer
def sys.read.next(
  file: File,
  step: Step.Read,
  rest: File -> String -> IO(Result<&1, &1, U32 & String, String>)
) -> IO(Result<&1, &1, U32 & String, String>):
  match step:
    case Step.ReadMore{text}:
      rest(file)(text)
    case Step.ReadStop{answer}:
      sys.read.end(file, answer)

# unpack a read's file and answer
def sys.read.un(
  got: String,
  rest: File -> String -> IO(Result<&1, &1, U32 & String, String>),
  pair: File & Result<&1, &1, U32 & String, String>
) -> IO(Result<&1, &1, U32 & String, String>):
  (file, res) = pair
  sys.read.next(file, Step.read.step(res, got), rest)

# read chunks until an empty one; fuel first, so the call is a decreasing one
def sys.read.go(
  fuel: Nat,
  file: File,
  got: String,
  +chunk: U32
) -> IO(Result<&1, &1, U32 & String, String>):
  match fuel:
    case 0n:
      sys.read.end(file, Step.read.spent())
    case 1n+f:
      IO.bind(File & Result<&1, &1, U32 & String, String>,
        Result<&1, &1, U32 & String, String>,
        File.read(file, chunk),
        pair => sys.read.un(got, fl => g => sys.read.go(f, fl, g, chunk), pair))

# the file's size decides the chunk; a failed size is the answer
def sys.read.sized(
  pair: File & Result<&1, &1, U32 & String, U32>
) -> IO(Result<&1, &1, U32 & String, String>):
  (file, res) = pair
  match res:
    case Fail{error}:
      sys.read.end(file, Fail{error})
    case Done{size}:
      sys.read.go(sys.read.fuel(), file, "", Step.read.chunk(size))

# an opened file is sized and read; a failed open is the answer
def sys.read.opened(
  res: Result<&1, &1, U32 & String, File>
) -> IO(Result<&1, &1, U32 & String, String>):
  match res:
    case Fail{error}:
      IO.pure(Result<&1, &1, U32 & String, String>, Fail{error})
    case Done{file}:
      IO.bind(File & Result<&1, &1, U32 & String, U32>,
        Result<&1, &1, U32 & String, String>, File.size(file), sys.read.sized)

# a whole file's text
def sys.read(path: String) -> IO(Result<&1, &1, U32 & String, String>):
  IO.bind(Result<&1, &1, U32 & String, File>,
    Result<&1, &1, U32 & String, String>, File.open(path, "r"),
    sys.read.opened)

# close the file, then answer the write's result
def sys.write.done(
  pair: File & Result<&1, &1, U32 & String, Unit>
) -> IO(Result<&1, &1, U32 & String, Unit>):
  (file, res) = pair
  IO.bind(Unit, Result<&1, &1, U32 & String, Unit>, File.close(file),
    _u => IO.pure(Result<&1, &1, U32 & String, Unit>, res))

# write to an opened file; a failed open is the answer
def sys.write.opened(
  text: String,
  res: Result<&1, &1, U32 & String, File>
) -> IO(Result<&1, &1, U32 & String, Unit>):
  match res:
    case Fail{error}:
      IO.pure(Result<&1, &1, U32 & String, Unit>, Fail{error})
    case Done{file}:
      IO.bind(File & Result<&1, &1, U32 & String, Unit>,
        Result<&1, &1, U32 & String, Unit>, File.write(file, text),
        sys.write.done)

# a file's whole text replaced (created when missing)
def sys.write(
  path: String,
  text: String
) -> IO(Result<&1, &1, U32 & String, Unit>):
  IO.bind(Result<&1, &1, U32 & String, File>,
    Result<&1, &1, U32 & String, Unit>, File.open(path, "w"),
    res => sys.write.opened(text, res))

# rename the written temporary file, or answer the write's failure
def sys.save.next(
  +path: String,
  step: Step.Save
) -> IO(Result<&1, &1, U32 & String, Unit>):
  match step:
    case Step.SaveMove{}:
      ezsys.rename(Step.save.tmp(path), path)
    case Step.SaveStop{error}:
      IO.pure(Result<&1, &1, U32 & String, Unit>, Fail{error})

# write `<path>.tmp`, then rename it over path
def sys.save(
  +path: String,
  text: String
) -> IO(Result<&1, &1, U32 & String, Unit>):
  IO.bind(Result<&1, &1, U32 & String, Unit>,
    Result<&1, &1, U32 & String, Unit>, sys.write(Step.save.tmp(path), text),
    res => sys.save.next(path, Step.save.step(res)))

# an environment variable, or the fallback when it is unset
def sys.env(name: String, fallback: String) -> IO(String):
  IO.bind(Result<&1, &1, U32 & String, String>, String, IO.get_env(name),
    res => IO.pure(String, Step.env.pick(res, fallback)))

# the wall clock's ISO 8601 UTC text
def sys.now_iso() -> IO(String):
  IO.bind(U32 & U32, String, ezsys.clock(),
    now => IO.pure(String, Clock.time.iso.of(now)))
