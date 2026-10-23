# ezsys

System helpers for [Bend 2](https://github.com/bendlang/bend): whole-file
reads and atomic saves, environment variables with a default, the wall
clock as ISO 8601 UTC, text templates, a directory's names, and a failed
file operation written as Python writes an `OSError`.

## Install

With [Bend](https://github.com/bendlang/bend) alone there is nothing to
install: import ezsys by its hub name and version, and `bend` fetches it
from [the hub](https://hub.bend-lang.com) into `~/.bend/lib` on the first
run; no install step. ezsys is built and checked on Bend 2.0.38.

```
import emerging-ezsys@0.1.0.0/main.bend as Sys
```

`emerging-ezsys@0.1.0.0` is ezsys v0.1.0, once the release is published.

Or with [ez](https://github.com/Emerging-Patterns/ez), which records the
package in `ez.toml` (`ez init` makes one):

```
ez add Emerging-Patterns/ezsys
```

## Usage

| Name | Type | What it does |
| :---- | :---- | :---- |
| `file.read(path)` | `IO(Result<&1, &1, U32 & String, String>)` | the whole file's text |
| `file.write(path, text)` | `IO(Result<&1, &1, U32 & String, Unit>)` | replaces the file's text, creating it when missing |
| `file.save(path, text)` | `IO(Result<&1, &1, U32 & String, Unit>)` | writes `path.tmp`, flushes it, renames it over `path` |
| `env.or(name, fallback)` | `IO(String)` | the variable's value, or `fallback` when it is unset |
| `time.now()` | `IO(U32 & U32)` | the wall clock: seconds since 1970-01-01T00:00:00Z and milliseconds |
| `time.iso(secs, ms)` | `String` | `YYYY-MM-DDTHH:MM:SS.mmmZ` |
| `time.now_iso()` | `IO(String)` | `time.iso` of `time.now()` |
| `text.fill(template, pairs)` | `String` | every `{{key}}` replaced by its value |
| `text.fill_with(open, close, template, pairs)` | `String` | the same with other delimiters |
| `text.strip(txt)`, `text.lstrip(txt)`, `text.rstrip(txt)` | `String` | Python's `str.strip()` and its two halves, with Python's whitespace (no-break space included) |
| `text.replace(txt, old, new)` | `String` | every `old` replaced, left to right, as `str.replace` |
| `text.split(txt, sep)` | `List<&2, String>` | the pieces between every `sep`, as `str.split(sep)` |
| `text.find(txt, needle)` | `Maybe<&2, U32>` | where `needle` first starts, in code points, as `str.find` (`None` for `-1`) |
| `text.lower(txt)`, `text.upper(txt)` | `String` | `str.lower()` and `str.upper()` for ASCII, Latin-1, Latin Extended-A, Greek and Cyrillic |
| `text.pad_right(txt, width)` | `String` | `str.ljust(width)` |
| `text.truncate(txt, width)` | `String` | `txt[:width]` |
| `digits.cmp(lhs, rhs)` | `Cmp` | two strings of digits in numeric order, any length |
| `dir.list(path)` | `IO(Result<&1, &1, U32 & String, List<&2, String>>)` | the directory's names, sorted, without `.` and `..` |
| `err.os(code, why, path)` | `String` | `[Errno 2] No such file or directory: '/tmp/x'` |

A failure is a value, Base's `Fail{(errno, message)}`, never an exit: match
on it, or hand it to `IO.try` to exit with it. `file.save` is the one to use
for a file another process reads: a reader sees the old text or the new,
never part of either, as long as `path` and `path.tmp` are on one
filesystem. `time.now()` holds every second up to 2106-02-07T06:28:15Z.

```
import Base
import emerging-ezsys@0.1.0.0/main.bend as Sys

def shown(res: Result<&1, &1, U32 & String, String>) -> String:
  match res:
    case Fail{(_code, why)}:
      "could not read it: " ++ why
    case Done{text}:
      text

def main() -> IO(Unit):
  do IO<Unit>:
    +path : String <- Sys.env.or("STATE_FILE", "/tmp/state.txt")
    +now : String <- Sys.time.now_iso()
    _saved : Result<&1, &1, U32 & String, Unit> <- Sys.file.save(path,
      Sys.text.fill("saved at {{when}}\n", [("when", now)]))
    back : Result<&1, &1, U32 & String, String> <- Sys.file.read(path)
    IO.print(shown(back))
```

A template marker is an open delimiter, a key and a close delimiter. A key
runs to the first close delimiter, so it matches exactly, spaces included,
and markers do not nest. A value is written as it is and never scanned
again. A key no pair has, and a marker with no close, are left as written.
`text.fill_with("<!--", "-->", shell, pairs)` fills the `<!--NAME-->`
markers of an HTML shell, which keeps the shell valid HTML before it is
filled.

`file.read` reads text: Bend's `File.read` decodes UTF-8 and writes U+FFFD
for an invalid byte. It asks for the file's size and reads it in one chunk
of at least that many bytes; a pipe or a file that grows while it is read
can take more than one, and a UTF-8 sequence cut between two chunks is read
as U+FFFD.

`dir.list` answers names, not paths, in code point order (the bytewise
order of their UTF-8, so `sorted(os.listdir(path))` in Python), with no `.`
or `..`; a symbolic link is listed by its own name and not followed. A name
that is not valid UTF-8 is answered with U+FFFD in place of the bad bytes.

`err.os(code, why, path)` writes a `Fail{(code, why)}` from a file operation
the way Python's `OSError` does: glibc's text for the common Linux codes
(the table is in SPEC.md), `why` for any other code, and the path as
Python's `repr` writes it.

`examples/smoke/main.bend` uses every helper:

```
git clone https://github.com/Emerging-Patterns/ezsys
cd ezsys
bend examples/smoke/main.bend -o smoke
SMOKE_DIR=/tmp ./smoke
```

## Guarantees

[SPEC.md](SPEC.md) lists every behavior ezsys guarantees, each either proved
by a quantified law in `LAWS.bend` or named as a trusted assumption. A row
marked pending is not guaranteed yet. `nix flake check` runs the proof gate
(`bend PROOF.bend` must print exactly `ALL PROOFS CHECK` first), the entry
check, the smoke program above on the C lane, and bolt, whose `trace` rule
checks that SPEC.md and the laws agree.

What is proved: the shape of every `time.iso` (24 characters, digits where
digits belong) and how it splits into the day's date and the time of day;
the leap and century rules at 2000, 2023, 2024 and 2100 and the boundaries
at 1970, 2000 and 2106; how a template's markers are replaced, kept or left
alone; every decision `file.read`, `file.save`, `env.or` and `dir.list`
make (which names `dir.list` answers, how many times, and in what order);
and how `err.os` writes a code and a path. What is trusted: the three
effects ezsys adds (a flush-and-rename, the wall clock and a directory's
names, each a C file with a JS twin), Base's file and environment effects,
and the IO that runs them in order. The calendar for every other day is
pending (SYS-TIME-5).

## License

MIT, see [LICENSE](LICENSE).
