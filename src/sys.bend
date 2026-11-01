# ezsys/src/sys: the effects. Every decision these make is src/step.bend's,
# src/clock.bend's or src/dir.bend's; this module runs the effects in order
# and acts on the answers. The three effects of its own are foreign code, a C
# file and its JS twin each: a flush-and-rename, the wall clock and a
# directory's names, each trusted above its def.
#
# Trusted, not proved (IO sequencing: effects are foreign, so the checker
# cannot run an IO program and no law can state what happens after an
# effect; every decision acted on is laws/ReadStepAccumulates.bend,
# laws/SaveWritesTmpThenRenames.bend, laws/EnvOrFallsBack.bend, the
# laws/Iso*.bend and laws/DirList*.bend guarantees):
# - this module acts on src/step.bend's, src/clock.bend's and src/dir.bend's
#   answers in order: `file.read` answers a failed open or size unchanged,
#   reads until the step stops, gives up with `EFBIG` after 65536 reads, and
#   closes every file it opened; `file.write` answers a failed open
#   unchanged, writes, closes, and answers the write's result; `file.save`
#   writes the temporary file with `file.write` and renames only on the
#   step's word; `env.or` picks from `IO.get_env`'s answer; `time.now_iso`
#   formats one reading of `time.now`; `dir.list` answers src/dir.bend's step
#   of one `ezsys.list` answer; main.bend's names call these and nothing else.
# - Base's effects `File.open`, `File.size`, `File.read`, `File.write`,
#   `File.close` and `IO.get_env` (foreign C and JS in Bend's runtime,
#   `effs/file_*.c` and `effs/get_env.c`, which no law reaches) report a
#   failure as `Fail` and never end the process themselves; `File.write`
#   writes the whole text; `File.read` decodes UTF-8 and writes U+FFFD for an
#   invalid byte; `IO.get_env` answers `Done` with the value, even an empty
#   one, exactly when the variable is set.
import Base
import ./step.bend as Step
import ./clock.bend as Clock
import ./dir.bend as Dir

# flush `from` to disk, then rename it over `to`. Base has no rename, and the
# services ezsys was written for renamed with `Process.run("mv", ...)`; `mv`
# is a second program found on `PATH` at run time, costs a fork and exec, can
# only report success as an exit status, cannot flush the file first, and
# falls back to copying and deleting across filesystems, which is not atomic.
#
# Trusted, not proved (foreign C and JS over `fsync(2)` and `rename(2)`,
# which no law reaches; the atomicity is the operating system's):
# `ezsys.rename(from, to)` (effs/rename.c, effs/rename.js) opens `from`,
# flushes it with `fsync`, closes it and renames it to `to` with `rename(2)`
# (`fs.renameSync` on the JS lane), so on one filesystem a reader of `to`
# sees its old text or the new, never part of either; across two it fails
# with `EXDEV`. It answers `Done{Unit{}}`, or `Fail{(errno, message)}` with
# nothing renamed when the open, the flush or the rename fails; it never ends
# the process. The directory is not flushed.
def ezsys.rename(
  from: String,
  to: String
) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "./effs/rename.c"
  import "./effs/rename.js"

# whole seconds since 1970-01-01T00:00:00Z and the milliseconds past them.
# An effect because Base's `IO.now()` is milliseconds since the process
# started, not the wall clock.
#
# Trusted, not proved (foreign C and JS over `clock_gettime(2)` and
# `Date.now()`; the time it answers is the host's): `ezsys.clock()`
# (effs/clock.c, effs/clock.js) answers the wall clock, `CLOCK_REALTIME`
# (`Date.now()` on the JS lane), as whole seconds since 1970-01-01T00:00:00Z
# cut to 32 bits and the milliseconds past them, from 0 to 999.
def ezsys.clock() -> IO(U32 & U32):
  import "./effs/clock.c"
  import "./effs/clock.js"

# the names in a directory as the host lists them, in its order. Base has no
# way to list a directory, and those services ran `find` with `Process.run`
# for it, a second program again.
#
# Trusted, not proved (foreign C and JS over `opendir(3)`, `readdir(3)` and
# `fs.readdirSync`; the names and their order are the host's, and every
# decision about them is laws/DirListKeepsEveryName.bend,
# laws/DirListSorted.bend and laws/DirListPassesFailure.bend):
# `ezsys.list(path)` (effs/dir.c, effs/dir.js) answers `Done` of the name of
# every entry in the directory at `path`, each once, in the host's order,
# with `.` and `..` or without them, or `Fail{(errno, message)}` when the
# directory cannot be opened or read (a path with a NUL fails with `EILSEQ`);
# it never ends the process. It follows no entry, so a symbolic link is
# listed by its own name, and the directory is closed before the answer. A
# name's bytes are decoded as UTF-8 with U+FFFD for an invalid sequence, so
# such a name cannot be opened again from the answer; Python's `os.listdir`
# keeps those bytes as lone surrogates instead.
def ezsys.list(
  path: String
) -> IO(Result<&1, &1, U32 & String, List<&2, String>>):
  import "./effs/dir.c"
  import "./effs/dir.js"

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

# a directory's names, less "." and "..", sorted; a failed read is the answer
def sys.list(
  path: String
) -> IO(Result<&1, &1, U32 & String, List<&2, String>>):
  IO.bind(Result<&1, &1, U32 & String, List<&2, String>>,
    Result<&1, &1, U32 & String, List<&2, String>>, ezsys.list(path),
    res => IO.pure(Result<&1, &1, U32 & String, List<&2, String>>,
      Dir.dir.step(res)))
