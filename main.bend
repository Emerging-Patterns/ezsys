# ezsys: system helpers for Bend 2: whole-file reads and atomic saves,
# environment variables with a default, the wall clock as ISO 8601 UTC, text
# templates, a directory's names, and a failure written as Python does.
# This file is the whole public interface; everything under src/ is
# internal.
import Base
import ./src/sys.bend as Sys
import ./src/clock.bend as Clock
import ./src/text.bend as Text
import ./src/errno.bend as Err

# a whole file's text; a failure to open or read it is a Fail, never an exit
def file.read(path: String) -> IO(Result<&1, &1, U32 & String, String>):
  Sys.sys.read(path)

# replace a file's whole text, creating it when it is missing
def file.write(
  path: String,
  text: String
) -> IO(Result<&1, &1, U32 & String, Unit>):
  Sys.sys.write(path, text)

# write `<path>.tmp`, flush it, and rename it over path, so a reader sees
# the old text or the new, never part of either
def file.save(
  path: String,
  text: String
) -> IO(Result<&1, &1, U32 & String, Unit>):
  Sys.sys.save(path, text)

# an environment variable's value (even an empty one), or fallback when it
# is unset
def env.or(name: String, fallback: String) -> IO(String):
  Sys.sys.env(name, fallback)

# the wall clock: whole seconds since 1970-01-01T00:00:00Z, and the
# milliseconds past them
def time.now() -> IO(U32 & U32):
  Sys.ezsys.clock()

# ISO 8601 UTC, `YYYY-MM-DDTHH:MM:SS.mmmZ`, of seconds since the epoch and a
# millisecond
def time.iso(secs: U32, ms: U32) -> String:
  Clock.time.iso(secs, ms)

# the wall clock as ISO 8601 UTC
def time.now_iso() -> IO(String):
  Sys.sys.now_iso()

# every `{{key}}` in a template replaced by its value; unknown and unclosed
# markers are left as written
def text.fill(template: String, pairs: List<(String & String)>) -> String:
  Text.text.fill(template, Text.text.own(pairs))

# the same with other delimiters, e.g. `<!--` and `-->`
def text.fill_with(
  open: String,
  close: String,
  template: String,
  pairs: List<(String & String)>
) -> String:
  Text.text.fill_with(open, close, template, Text.text.own(pairs))

# a directory's names, sorted by code point, with no "." or ".."; a failure
# to read it is a Fail, never an exit
def dir.list(
  path: String
) -> IO(Result<&1, &1, U32 & String, List<&2, String>>):
  Sys.sys.list(path)

# a failed file operation as Python's OSError writes it:
# `[Errno 2] No such file or directory: '/tmp/x'`
def err.os(code: U32, why: String, path: String) -> String:
  Err.err.os(code, why, path)
