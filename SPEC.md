# ezsys specification

This is the list of every behavior ezsys guarantees, each under a stable requirement ID. Every requirement has one of two levels. A **Proved** requirement holds for every input, and is backed by a quantified law (a `for` or `exs` binder) in `LAWS.bend` that passes the proof gate. A **Trusted** requirement is an assumption ezsys cannot check from inside its own gate, and it is listed in the trust boundary below. A Proved requirement whose laws have not all landed has status **pending**: we intend to prove it, and until then it is not guaranteed. The proof gate is this check: the first line `bend PROOF.bend` prints is exactly `ALL PROOFS CHECK`. Tests and fixtures are never evidence for a requirement.

The requirements are about the public interface in `main.bend`. Its pure functions are thin names for the functions in `src/text.bend` and `src/clock.bend`, which `ENTRY.bend` states laws for, and every decision its IO functions make is a function in `src/step.bend`; those three modules do no IO, so `LAWS.bend` and `PROOF.bend` import them and nothing else. `src/sys.bend` runs the effects and acts on the answers (SYS-TRUST-4). It is the only module with foreign code: one effect that flushes and renames a file (SYS-TRUST-1) and one that reads the wall clock (SYS-TRUST-2).

Base has no rename, and the services ezsys was written for renamed with `Process.run("mv", ...)`. ezsys adds an effect instead, a C file and its JS twin, because `mv` is a second program found on `PATH` at run time, costs a fork and exec, can only report success as an exit status, cannot flush the file first, and falls back to copying and deleting when the two names are on different filesystems, which is not atomic. `rename(2)` is one system call that is atomic on one filesystem and fails with `EXDEV` across two, and the effect flushes the file with `fsync(2)` before it renames it. The clock is an effect for the same reason: Base's `IO.now()` is milliseconds since the process started, not the wall clock.

## Format

A requirement table is any table whose header row is exactly `| ID | Requirement | Level | Status | Law |`. An ID is uppercase segments joined by hyphens, at least two (`[A-Z][A-Z0-9]*(-[A-Z0-9]+)+`), unique within the requirement tables, and never reused once released. Level is `Proved` or `Trusted`. Status is `proved` or `pending` for a Proved row and empty for a Trusted row. A Law cell holds `<path> <law>` entries, paths relative to this file, separated by `; `. A proved row names one or more laws, and together they prove it. A pending row may name laws that each prove part of it; the row stays pending until its requirement is proved in full, and "Left to prove" says what is missing.

A law proves a requirement when a comment line `# <ID>`, alone on its line, sits in the unbroken comment block directly above its `law` line. A law may carry several tags, one per line:

```
# LAW: a template with no marker is left unchanged
# SYS-TEXT-1
law fill_unmarked:
```

A tag may name a proved or a pending requirement, never a Trusted one or an ID no requirement table lists. bolt's `trace` rule checks all of this over the whole tree, and its `closed` rule rejects a law with no binder; both are errors in `bolt.bend`.

## Requirements

### Files (SYS-FILE)

`file.read`, `file.write` and `file.save` answer `Result<&1, &1, U32 & String, A>`, Base's own shape: a failure is `Fail{(errno, message)}` and is a value, never an exit. `file.read` opens the file, asks its size, and reads chunks of at least that many bytes (and at least 64 KiB) until a read answers an empty chunk.

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SYS-FILE-1 | For every answer of one read and every text read before it, `file.read`'s step stops with that answer's failure unchanged when the read failed; stops with exactly the text read before it when the read answered an empty chunk; and otherwise reads on with the text read before it followed by the chunk. | Proved | proved | LAWS.bend read_fail; LAWS.bend read_end; LAWS.bend read_more |
| SYS-FILE-2 | For every path, `file.save` writes its text to exactly `path ++ ".tmp"`; when that write fails it answers the failure unchanged and renames nothing, and when it succeeds it renames exactly `path ++ ".tmp"` to exactly `path` and answers the rename's result. | Proved | proved | LAWS.bend save_tmp; LAWS.bend save_fail; LAWS.bend save_move |
| SYS-TRUST-1 | `ezsys.rename(from, to)` (`src/effs/rename.c`, `src/effs/rename.js`) opens `from`, flushes it with `fsync`, closes it and renames it to `to` with `rename(2)` (`fs.renameSync` on the JS lane), so on one filesystem a reader of `to` sees its old text or the new, never part of either. It answers `Done{Unit{}}`, or `Fail{(errno, message)}` with nothing renamed when the open, the flush or the rename fails; it never ends the process. The directory is not flushed. | Trusted | | |
| SYS-TRUST-3 | Base's effects `File.open`, `File.size`, `File.read`, `File.write`, `File.close` and `IO.get_env` report a failure as `Fail` and never end the process themselves; `File.write` writes the whole text; `File.read` decodes UTF-8 and writes U+FFFD for an invalid byte; `IO.get_env` answers `Done` with the value, even an empty one, exactly when the variable is set. | Trusted | | |

### Environment (SYS-ENV)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SYS-ENV-1 | For every name and fallback, `env.or(name, fallback)` answers the variable's value when it is set, even when that value is empty, and exactly `fallback` when it is not. | Proved | proved | LAWS.bend env_set; LAWS.bend env_unset |

### Wall clock (SYS-TIME)

`time.now()` answers whole seconds since 1970-01-01T00:00:00Z as a `U32`, which holds every second up to 2106-02-07T06:28:15Z, and the milliseconds past that second. `time.iso(secs, ms)` writes them as ISO 8601 UTC, `YYYY-MM-DDTHH:MM:SS.mmmZ`, with the proleptic Gregorian calendar of Howard Hinnant's `civil_from_days`; the milliseconds are written as their last three decimal places. `time.now_iso()` is `time.iso` of `time.now()` (SYS-TRUST-4). Years before 1970, 1900 among them, are outside the input, so the century rule is checked at 2100 instead.

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SYS-TIME-1 | For every `secs` and `ms`, `time.iso(secs, ms)` is exactly 24 characters, of the form `####-##-##T##:##:##.###Z` where each `#` is an ASCII digit `0` to `9`. | Proved | proved | LAWS.bend iso_shape; LAWS.bend iso_width |
| SYS-TIME-2 | For every `secs` and `ms`, `time.iso(secs, ms)` is the date of day `secs / 86400`, then `T`, then two digits each of `secs % 86400 / 3600`, `secs % 86400 % 3600 / 60` and `secs % 86400 % 60` joined by `:`, then `.`, three digits of `ms` and `Z`; the date is four digits of the year, `-`, two of the month, `-`, two of the day. So every instant of one UTC day carries the same date. | Proved | proved | LAWS.bend iso_split; LAWS.bend clock_fields; LAWS.bend date_fields |
| SYS-TIME-3 | For every `secs` in the day and every `ms`, the leap and century rules hold at these days: day 11016 is 2000-02-29 and day 11017 is 2000-03-01 (2000 is divisible by 400), day 19782 is 2024-02-29 and day 19783 is 2024-03-01 (divisible by 4), day 19416 is 2023-02-28 and day 19417 is 2023-03-01 (not divisible by 4), and day 47540 is 2100-02-28 and day 47541 is 2100-03-01 (divisible by 100, not by 400). | Proved | proved | LAWS.bend leap_2000; LAWS.bend leap_2000_after; LAWS.bend leap_2024; LAWS.bend leap_2024_after; LAWS.bend common_2023; LAWS.bend common_2023_after; LAWS.bend century_2100; LAWS.bend century_2100_after |
| SYS-TIME-4 | For every `secs` in the day and every `ms`, the boundaries of the input and of a millennium fall where they belong: day 0 is 1970-01-01, day 10956 is 1999-12-31, day 10957 is 2000-01-01, and day 49710 is 2106-02-07; and for every `ms`, the last second, 4294967295, is `2106-02-07T06:28:15`. | Proved | proved | LAWS.bend epoch; LAWS.bend eve_2000; LAWS.bend day_2000; LAWS.bend last_day; LAWS.bend last_second |
| SYS-TIME-5 | For every day number `d` from 0 to 49710, `time.iso` writes day `d` as the proleptic Gregorian date `d` days after 1970-01-01. | Proved | pending | LAWS.bend leap_2000; LAWS.bend leap_2000_after; LAWS.bend leap_2024; LAWS.bend leap_2024_after; LAWS.bend common_2023; LAWS.bend common_2023_after; LAWS.bend century_2100; LAWS.bend century_2100_after; LAWS.bend epoch; LAWS.bend eve_2000; LAWS.bend day_2000; LAWS.bend last_day |
| SYS-TRUST-2 | `ezsys.clock()` (`src/effs/clock.c`, `src/effs/clock.js`) answers the wall clock, `CLOCK_REALTIME` (`Date.now()` on the JS lane), as whole seconds since 1970-01-01T00:00:00Z cut to 32 bits and the milliseconds past them, from 0 to 999. | Trusted | | |

### Text templates (SYS-TEXT)

A marker is an open delimiter, a key and a close delimiter. `text.fill(template, pairs)` uses `{{` and `}}`, so `{{name}}` is the marker for the key `name`; `text.fill_with(open, close, template, pairs)` takes the delimiters, so the whole-line `<!--NAME-->` markers of a page shell are `text.fill_with("<!--", "-->", shell, pairs)`. The scan reads the template once, left to right: at an open delimiter a key starts, and it runs to the first close delimiter after it, so keys are matched exactly (spaces included) and markers do not nest. A key's value is the value of the first pair with that key, and it is written as it is, never scanned again. A key no pair has, and a marker with no close delimiter, are left as written. An empty delimiter marks nothing. The laws state these for `src/text.bend`'s `text.fill_with`, which takes the pairs as a reusable list; `main.bend` copies the caller's pairs into one in order (SYS-TEXT-6). `O` and `C` below are any nonempty open and close delimiters.

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SYS-TEXT-1 | For every template in which no open delimiter starts (`text.marked` is false), and for every template when either delimiter is empty, `text.fill_with` answers the template unchanged. | Proved | proved | LAWS.bend fill_unmarked; LAWS.bend fill_open_empty; LAWS.bend fill_close_empty |
| SYS-TEXT-2 | For every character `h` and text `t` such that `O` does not start at `h`, filling `h` followed by `t` is `h` followed by filling `t`. | Proved | proved | LAWS.bend fill_plain |
| SYS-TEXT-3 | For every key with a value `v`, in which no `C` starts before the close delimiter that follows it (`text.free`), and every text `rest`, filling `O ++ key ++ C ++ rest` is exactly `v` followed by filling `rest`. | Proved | proved | LAWS.bend fill_known |
| SYS-TEXT-4 | For every key no pair has, in which no `C` starts before the close delimiter that follows it, and every text `rest`, filling `O ++ key ++ C ++ rest` is exactly `O ++ key ++ C` followed by filling `rest`. | Proved | proved | LAWS.bend fill_unknown |
| SYS-TEXT-5 | For every key in which no `C` starts (`text.marked` of `C` is false), filling `O ++ key` (a marker with no close) is exactly `O ++ key`. | Proved | proved | LAWS.bend fill_unclosed |
| SYS-TEXT-6 | A key's value is the value of the first pair whose key equals it, and there is none when no pair has the key; the caller's pairs are kept in their order. | Proved | proved | LAWS.bend value_none; LAWS.bend value_hit; LAWS.bend value_miss; LAWS.bend own_order |
| SYS-TEXT-7 | For every template and pairs, `text.fill` is `text.fill_with` with `{{` and `}}`. | Proved | proved | LAWS.bend fill_braces |

### IO sequencing (SYS-TRUST)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SYS-TRUST-4 | `src/sys.bend` acts on `src/step.bend`'s and `src/clock.bend`'s answers in order: `file.read` answers a failed open or size unchanged, reads until the step stops, gives up with `EFBIG` after 65536 reads, and closes every file it opened; `file.write` answers a failed open unchanged, writes, closes, and answers the write's result; `file.save` writes the temporary file with `file.write` and renames only on the step's word; `env.or` picks from `IO.get_env`'s answer; `time.now_iso` formats one reading of `time.now`; `main.bend`'s names call these and nothing else. | Trusted | | |

## Trust boundary

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| SYS-TRUST-1 | `ezsys.rename` flushes `from` and renames it to `to`, atomically on one filesystem, and reports a failure as `Fail`. | It is foreign C and JS (`src/effs/rename.c`, `src/effs/rename.js`) over `fsync(2)` and `rename(2)`, which no law reaches. The atomicity is the operating system's. |
| SYS-TRUST-2 | `ezsys.clock` answers the wall clock as U32 seconds and milliseconds 0 to 999. | It is foreign C and JS (`src/effs/clock.c`, `src/effs/clock.js`) over `clock_gettime(2)` and `Date.now()`, and the time it answers is the host's. |
| SYS-TRUST-3 | Base's file and environment effects behave as the requirement states. | They are foreign C and JS in Bend's runtime (`effs/file_*.c`, `effs/get_env.c`), which no law reaches. |
| SYS-TRUST-4 | `src/sys.bend` acts on the pure modules' answers in order, as the requirement states. | It is IO sequencing: effects are foreign, so the checker cannot run an IO program and no law can state what happens after an effect. Every decision it acts on is SYS-FILE-1, SYS-FILE-2, SYS-ENV-1 or SYS-TIME-1 to 5. |

## Left to prove

| ID | What is proved | What is missing |
| :---- | :---- | :---- |
| SYS-TIME-5 | The date of each day SYS-TIME-3 and SYS-TIME-4 name, for every instant of it. | Every other day. A proof for every `d` needs lemmas on U32 division that Base does not have, and a law that walks all 49711 days runs out of time in the checker (1000 days took 55 s). Until then the anchors, and the shape and split of SYS-TIME-1 and SYS-TIME-2, are what is proved. |
