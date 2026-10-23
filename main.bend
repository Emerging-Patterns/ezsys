# ezsys: system helpers for Bend 2: whole-file reads and atomic saves,
# environment variables with a default, the wall clock as ISO 8601 UTC, text
# templates, Python's str helpers (strip, replace, split, find, case,
# width, digit order), a directory's names, and a failure written as
# Python does.
# This file is the whole public interface; everything under src/ is
# internal.
import Base
import ./src/sys.bend as Sys
import ./src/clock.bend as Clock
import ./src/text.bend as Text
import ./src/errno.bend as Err
import ./src/str.bend as Str

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

# the civil fields of seconds since the epoch, in UTC: year, month, day,
# hour, minute, second and ISO weekday (1 Monday to 7 Sunday)
def time.civil(secs: U32) -> U32 & U32 & U32 & U32 & U32 & U32 & U32:
  Clock.time.fields(secs)

# the ISO 8601 week-numbering year and week of seconds since the epoch
def time.iso_week(secs: U32) -> U32 & U32:
  Clock.time.iso_week(secs)

# the ISO 8601 week as `date -u +%G-W%V` writes it, e.g. `2026-W43`
def time.iso_week_text(secs: U32) -> String:
  Clock.time.iso_week_text(secs)

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


# the text with Python's whitespace removed from both ends (str.strip())
def text.strip(txt: String) -> String:
  Str.text.strip(txt)

# the text with Python's whitespace removed from its start (str.lstrip())
def text.lstrip(txt: String) -> String:
  Str.text.lstrip(txt)

# the text with Python's whitespace removed from its end (str.rstrip())
def text.rstrip(txt: String) -> String:
  Str.text.rstrip(txt)

# every `old` replaced by `new`, left to right, never overlapping
# (str.replace); an empty `old` puts `new` around every character
def text.replace(txt: String, old: String, new: String) -> String:
  Str.text.replace(txt, old, new)

# the pieces between every `sep` (str.split(sep)); an empty `sep` answers
# the text as its one piece
def text.split(txt: String, sep: String) -> List<&2, String>:
  Str.text.split(txt, sep)

# the index in code points where `needle` first starts, or None
# (str.find)
def text.find(txt: String, needle: String) -> Maybe<&2, U32>:
  Str.text.find(txt, needle)

# the text in lowercase (str.lower) for ASCII, Latin-1, Latin Extended-A,
# Greek and Cyrillic; other code points are kept
def text.lower(txt: String) -> String:
  Str.text.lower(txt)

# the text in uppercase (str.upper) for ASCII, Latin-1, Latin Extended-A,
# Greek and Cyrillic; other code points are kept
def text.upper(txt: String) -> String:
  Str.text.upper(txt)

# the text with spaces after it up to `width` code points (str.ljust)
def text.pad_right(txt: String, width: Nat) -> String:
  Str.text.pad_right(txt, width)

# the first `width` code points of the text (txt[:width])
def text.truncate(txt: String, width: Nat) -> String:
  Str.text.truncate(txt, width)

# two strings of ASCII digits in numeric order, any length
def digits.cmp(lhs: String, rhs: String) -> Cmp:
  Str.text.digits.cmp(lhs, rhs)

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
