# ezsys: the laws. Each law carries the SPEC.md row it proves, or proves part
# of, on its own comment line. PROOF.bend fills them; `bend PROOF.bend` is
# the gate. Only the pure modules are imported: src/sys.bend holds foreign
# code, and no file that reaches it can print ALL PROOFS CHECK.
import Base
import ./src/step.bend as Step
import ./src/clock.bend as Clock
import ./src/text.bend as Text
import ./src/dir.bend as Dir
import ./src/errno.bend as Err

# --- the specification's own words ---

# an ASCII digit becomes '#', any other character stays
def shape.char(chr: Char) -> Char:
  match chr:
    case Chr{+x}:
      Bool.pick(Char, Bool.and((x >= 48 : U32), (x <= 57 : U32)), '#', Chr{x})

# a text with every ASCII digit made '#'
def shape(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{hd, tl}:
      SCon{shape.char(hd), shape(tl)}

# the form of every time.iso
def shape.iso() -> String:
  "####-##-##T##:##:##.###Z"

# --- files (SYS-FILE) ---

# LAW: a read that fails stops with its failure unchanged
# SYS-FILE-1
law read_fail:
  for code: U32
  for why: String
  for got: String
  {Step.read.step(Fail{(code, why)}, got) == Step.ReadStop{Fail{(code, why)}}
    : Step.Read}

# LAW: an empty chunk stops with exactly the text read before it
# SYS-FILE-1
law read_end:
  for got: String
  {Step.read.step(Done{""}, got) == Step.ReadStop{Done{got}} : Step.Read}

# LAW: any other chunk is appended to the text read before it
# SYS-FILE-1
law read_more:
  for h: Char
  for t: String
  for got: String
  {Step.read.step(Done{SCon{h, t}}, got) == Step.ReadMore{got ++ SCon{h, t}}
    : Step.Read}

# LAW: file.save writes to the path with .tmp after it
# SYS-FILE-2
law save_tmp:
  for path: String
  {Step.save.tmp(path) == path ++ ".tmp" : String}

# LAW: a failed write of the temporary file is the answer, and nothing is
# renamed
# SYS-FILE-2
law save_fail:
  for code: U32
  for why: String
  {Step.save.step(Fail{(code, why)}) == Step.SaveStop{(code, why)} : Step.Save}

# LAW: a written temporary file is renamed
# SYS-FILE-2
law save_move:
  for u: Unit
  {Step.save.step(Done{u}) == Step.SaveMove{} : Step.Save}

# --- environment (SYS-ENV) ---

# LAW: a set variable's value is the answer, even an empty one
# SYS-ENV-1
law env_set:
  for value: String
  for fallback: String
  {Step.env.pick(Done{value}, fallback) == value : String}

# LAW: an unset variable answers the fallback
# SYS-ENV-1
law env_unset:
  for code: U32
  for why: String
  for fallback: String
  {Step.env.pick(Fail{(code, why)}, fallback) == fallback : String}

# --- wall clock (SYS-TIME) ---

# LAW: every time.iso has the form ####-##-##T##:##:##.###Z, # a digit
# SYS-TIME-1
law iso_shape:
  for +secs: U32
  for +ms: U32
  {shape(Clock.time.iso(secs, ms)) == shape.iso() : String}

# LAW: every time.iso is 24 characters
# SYS-TIME-1
law iso_width:
  for secs: U32
  for ms: U32
  {String.length(Clock.time.iso(secs, ms)) == 24n : Nat}

# LAW: the date is the day's, then T and the time of day
# SYS-TIME-2
law iso_split:
  for secs: U32
  for ms: U32
  {Clock.time.iso(secs, ms) == Clock.time.date((secs / 86400 : U32))
    ++ "T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: the time of day is hours, minutes and seconds of the second of the
# day, then the milliseconds
# SYS-TIME-2
law clock_fields:
  for sod: U32
  for ms: U32
  {Clock.time.clock(sod, ms) == Clock.time.two((sod / 3600 : U32)) ++ ":"
    ++ Clock.time.two((sod % 3600 / 60 : U32)) ++ ":"
    ++ Clock.time.two((sod % 60 : U32)) ++ "." ++ Clock.time.three(ms) ++ "Z"
    : String}

# LAW: the date is four digits of the year, two of the month and two of the
# day of the day number
# SYS-TIME-2
law date_fields:
  for days: U32
  {Clock.time.date(days) == Clock.time.ymd.of(Clock.time.civil(days))
    : String}

# LAW: day 11016 is 2000-02-29, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law leap_2000:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 11016 : U32}
  {Clock.time.iso(secs, ms)
    == "2000-02-29T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 11017 is 2000-03-01, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law leap_2000_after:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 11017 : U32}
  {Clock.time.iso(secs, ms)
    == "2000-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 19782 is 2024-02-29, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law leap_2024:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 19782 : U32}
  {Clock.time.iso(secs, ms)
    == "2024-02-29T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 19783 is 2024-03-01, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law leap_2024_after:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 19783 : U32}
  {Clock.time.iso(secs, ms)
    == "2024-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 19416 is 2023-02-28, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law common_2023:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 19416 : U32}
  {Clock.time.iso(secs, ms)
    == "2023-02-28T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 19417 is 2023-03-01, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law common_2023_after:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 19417 : U32}
  {Clock.time.iso(secs, ms)
    == "2023-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 47540 is 2100-02-28, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law century_2100:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 47540 : U32}
  {Clock.time.iso(secs, ms)
    == "2100-02-28T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 47541 is 2100-03-01, at every second of it
# SYS-TIME-3
# SYS-TIME-5
law century_2100_after:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 47541 : U32}
  {Clock.time.iso(secs, ms)
    == "2100-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 0 is 1970-01-01, at every second of it
# SYS-TIME-4
# SYS-TIME-5
law epoch:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 0 : U32}
  {Clock.time.iso(secs, ms)
    == "1970-01-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 10956 is 1999-12-31, at every second of it
# SYS-TIME-4
# SYS-TIME-5
law eve_2000:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 10956 : U32}
  {Clock.time.iso(secs, ms)
    == "1999-12-31T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 10957 is 2000-01-01, at every second of it
# SYS-TIME-4
# SYS-TIME-5
law day_2000:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 10957 : U32}
  {Clock.time.iso(secs, ms)
    == "2000-01-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: day 49710 is 2106-02-07, at every second of it
# SYS-TIME-4
# SYS-TIME-5
law last_day:
  for secs: U32
  for ms: U32
  for e: {(secs / 86400 : U32) == 49710 : U32}
  {Clock.time.iso(secs, ms)
    == "2106-02-07T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}

# LAW: the last second a U32 holds is 2106-02-07T06:28:15
# SYS-TIME-4
law last_second:
  for ms: U32
  {Clock.time.iso(4294967295, ms)
    == "2106-02-07T06:28:15." ++ Clock.time.three(ms) ++ "Z" : String}

# --- text templates (SYS-TEXT) ---

# LAW: a template with no open delimiter in it is unchanged
# SYS-TEXT-1
law fill_unmarked:
  for open: String
  for close: String
  for t: String
  for pairs: Text.text.Pairs()
  for e: {Text.text.marked(open, t) == False{} : Bool}
  {Text.text.fill_with(open, close, t, pairs) == t : String}

# LAW: an empty open delimiter marks nothing
# SYS-TEXT-1
law fill_open_empty:
  for close: String
  for t: String
  for pairs: Text.text.Pairs()
  {Text.text.fill_with("", close, t, pairs) == t : String}

# LAW: an empty close delimiter marks nothing
# SYS-TEXT-1
law fill_close_empty:
  for open: String
  for t: String
  for pairs: Text.text.Pairs()
  {Text.text.fill_with(open, "", t, pairs) == t : String}

# LAW: a character where no open delimiter starts is written as it is
# SYS-TEXT-2
law fill_plain:
  for oh: Char
  for ot: String
  for ch: Char
  for ct: String
  for h: Char
  for t: String
  for pairs: Text.text.Pairs()
  for e: {String.starts_with(SCon{h, t}, SCon{oh, ot}) == False{} : Bool}
  {Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, SCon{h, t}, pairs)
    == SCon{h, Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, t, pairs)}
    : String}

# LAW: a marker whose key has a value is replaced by exactly that value
# SYS-TEXT-3
law fill_known:
  for +oh: Char
  for +ot: String
  for +ch: Char
  for +ct: String
  for +key: String
  for +value: String
  for +rest: String
  for +pairs: Text.text.Pairs()
  for +found: {Text.text.value(pairs, key) == Some{value} : Maybe<&2, String>}
  for +free: {Text.text.free(SCon{ch, ct}, key, SCon{ch, ct} ++ rest) == True{}
    : Bool}
  {Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct},
    SCon{oh, ot} ++ (key ++ (SCon{ch, ct} ++ rest)), pairs)
    == value ++ Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, rest, pairs)
    : String}

# LAW: a marker whose key has no value is left as written
# SYS-TEXT-4
law fill_unknown:
  for +oh: Char
  for +ot: String
  for +ch: Char
  for +ct: String
  for +key: String
  for +rest: String
  for +pairs: Text.text.Pairs()
  for +missing: {Text.text.value(pairs, key) == None{} : Maybe<&2, String>}
  for +free: {Text.text.free(SCon{ch, ct}, key, SCon{ch, ct} ++ rest) == True{}
    : Bool}
  {Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct},
    SCon{oh, ot} ++ (key ++ (SCon{ch, ct} ++ rest)), pairs)
    == (SCon{oh, ot} ++ (key ++ SCon{ch, ct}))
    ++ Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, rest, pairs) : String}

# LAW: a marker with no close delimiter is left as written
# SYS-TEXT-5
law fill_unclosed:
  for +oh: Char
  for +ot: String
  for +ch: Char
  for +ct: String
  for +key: String
  for +pairs: Text.text.Pairs()
  for +e: {Text.text.marked(SCon{ch, ct}, key) == False{} : Bool}
  {Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, SCon{oh, ot} ++ key, pairs)
    == SCon{oh, ot} ++ key : String}

# LAW: no pairs, no value
# SYS-TEXT-6
law value_none:
  for key: String
  {Text.text.value([], key) == None{} : Maybe<&2, String>}

# LAW: the first pair with the key gives its value
# SYS-TEXT-6
law value_hit:
  for k: String
  for v: String
  for rest: Text.text.Pairs()
  for key: String
  for e: {String.eq(k, key) == True{} : Bool}
  {Text.text.value((k, v) <> rest, key) == Some{v} : Maybe<&2, String>}

# LAW: a pair with another key is passed over
# SYS-TEXT-6
law value_miss:
  for k: String
  for v: String
  for rest: Text.text.Pairs()
  for key: String
  for e: {String.eq(k, key) == False{} : Bool}
  {Text.text.value((k, v) <> rest, key) == Text.text.value(rest, key)
    : Maybe<&2, String>}

# LAW: the caller's pairs are kept in their order
# SYS-TEXT-6
law own_order:
  for k: String
  for v: String
  for rest: List<(String & String)>
  {Text.text.own((k, v) <> rest) == (k, v) <> Text.text.own(rest)
    : Text.text.Pairs()}

# LAW: text.fill is text.fill_with with {{ and }}
# SYS-TEXT-7
law fill_braces:
  for t: String
  for pairs: Text.text.Pairs()
  {Text.text.fill(t, pairs) == Text.text.fill_with("{{", "}}", t, pairs)
    : String}

# --- directories (SYS-DIR) ---

# one copy of the name, when hit holds
def listed.pick(hit: Bool, count: Nat) -> Nat:
  match hit:
    case True{}:
      1n+count
    case False{}:
      count

# how many times a list holds a name
def listed(+name: String, xs: List<&2, String>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      listed.pick(String.eq(x, name), listed(name, rest))

# whether every name after prev is no greater than the one before it
def ascending.from(xs: List<&2, String>, +prev: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(String.is_le(prev, y), ascending.from(rest, y))

# whether every name is no greater by String.order than the one after it
def ascending(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      ascending.from(rest, x)

# LAW: a name that is neither . nor .. is answered as many times as the raw
# names hold it, and . and .. never
# SYS-DIR-1
law dir_count:
  for +raw: List<&2, String>
  for +name: String
  {listed(name, Dir.dir.names(raw))
    == Bool.pick(Nat, Bool.or(String.eq(name, "."), String.eq(name, "..")),
      0n, listed(name, raw)) : Nat}

# LAW: the answer is ascending by String.order
# SYS-DIR-2
law dir_sorted:
  for raw: List<&2, String>
  {ascending(Dir.dir.names(raw)) == True{} : Bool}

# LAW: a failed directory read is the answer unchanged
# SYS-DIR-3
law dir_fail:
  for code: U32
  for why: String
  {Dir.dir.step(Fail{(code, why)}) == Fail{(code, why)}
    : Result<&1, &1, U32 & String, List<&2, String>>}

# LAW: a directory read's names are answered as dir.names gives them
# SYS-DIR-3
law dir_done:
  for raw: List<&2, String>
  {Dir.dir.step(Done{raw}) == Done{Dir.dir.names(raw)}
    : Result<&1, &1, U32 & String, List<&2, String>>}

# --- errors (SYS-ERR) ---

# the common Linux codes and glibc's text for each, as Python's os.strerror
# gives it
def strerror() -> Err.err.Table():
  [
    (1, "Operation not permitted"),
    (2, "No such file or directory"),
    (3, "No such process"),
    (4, "Interrupted system call"),
    (5, "Input/output error"),
    (6, "No such device or address"),
    (7, "Argument list too long"),
    (8, "Exec format error"),
    (9, "Bad file descriptor"),
    (10, "No child processes"),
    (11, "Resource temporarily unavailable"),
    (12, "Cannot allocate memory"),
    (13, "Permission denied"),
    (14, "Bad address"),
    (15, "Block device required"),
    (16, "Device or resource busy"),
    (17, "File exists"),
    (18, "Invalid cross-device link"),
    (19, "No such device"),
    (20, "Not a directory"),
    (21, "Is a directory"),
    (22, "Invalid argument"),
    (23, "Too many open files in system"),
    (24, "Too many open files"),
    (25, "Inappropriate ioctl for device"),
    (26, "Text file busy"),
    (27, "File too large"),
    (28, "No space left on device"),
    (29, "Illegal seek"),
    (30, "Read-only file system"),
    (31, "Too many links"),
    (32, "Broken pipe"),
    (33, "Numerical argument out of domain"),
    (34, "Numerical result out of range"),
    (35, "Resource deadlock avoided"),
    (36, "File name too long"),
    (37, "No locks available"),
    (38, "Function not implemented"),
    (39, "Directory not empty"),
    (40, "Too many levels of symbolic links"),
    (84, "Invalid or incomplete multibyte or wide character"),
    (95, "Operation not supported"),
    (110, "Connection timed out"),
    (111, "Connection refused"),
    (112, "Host is down"),
    (113, "No route to host"),
    (116, "Stale file handle"),
    (122, "Disk quota exceeded"),
    (125, "Operation canceled")
  ]

# the hex digit at a place of "0123456789abcdef", '0' past it
def hexc(place: U32) -> Char:
  Err.err.hex.or(String.get("0123456789abcdef", U32.to_nat(place)))

# LAW: a code's text is looked up in strerror, with why for a code it lacks
# SYS-ERR-1
law err_table:
  for +code: U32
  for +why: String
  {Err.err.text(code, why) == Err.err.look(strerror(), code, why) : String}

# LAW: a code no entry has is written with why
# SYS-ERR-1
law look_none:
  for +code: U32
  for +why: String
  {Err.err.look(Nil{}, code, why) == why : String}

# LAW: the first entry with the code gives its text
# SYS-ERR-1
law look_hit:
  for k: U32
  for text: String
  for rest: Err.err.Table()
  for +code: U32
  for +why: String
  for e: {U32.is_eq(code, k) == True{} : Bool}
  {Err.err.look(Con{(k, text), rest}, code, why) == text : String}

# LAW: an entry with another code is passed over
# SYS-ERR-1
law look_miss:
  for k: U32
  for text: String
  for rest: Err.err.Table()
  for +code: U32
  for +why: String
  for e: {U32.is_eq(code, k) == False{} : Bool}
  {Err.err.look(Con{(k, text), rest}, code, why)
    == Err.err.look(rest, code, why) : String}

# LAW: [Errno N] text: repr(path)
# SYS-ERR-2
law err_os:
  for +code: U32
  for +why: String
  for +path: String
  {Err.err.os(code, why, path) == "[Errno " ++ U32.show(code) ++ "] "
    ++ Err.err.text(code, why) ++ ": " ++ Err.err.repr(path) : String}

# LAW: repr is the quote, the escaped characters and the quote
# SYS-ERR-3
law repr_shape:
  for +path: String
  {Err.err.repr(path) == SCon{Err.err.quote(path),
    Err.err.go(Err.err.quote(path), path)
      ++ SCon{Err.err.quote(path), SNil{}}} : String}

# LAW: a path with a ' and no " is quoted with "
# SYS-ERR-3
law quote_double:
  for +path: String
  for one: {String.contains(path, "'") == True{} : Bool}
  for two: {String.contains(path, "\"") == False{} : Bool}
  {Err.err.quote(path) == '"' : Char}

# LAW: a path with no ' is quoted with '
# SYS-ERR-3
law quote_plain:
  for +path: String
  for e: {String.contains(path, "'") == False{} : Bool}
  {Err.err.quote(path) == '\'' : Char}

# LAW: a path with a " is quoted with '
# SYS-ERR-3
law quote_both:
  for +path: String
  for e: {String.contains(path, "\"") == True{} : Bool}
  {Err.err.quote(path) == '\'' : Char}

# LAW: no characters are written as nothing
# SYS-ERR-3
law go_empty:
  for +q: Char
  {Err.err.go(q, "") == "" : String}

# LAW: the characters are escaped one by one, in order
# SYS-ERR-3
law go_char:
  for +q: Char
  for c: Char
  for t: String
  {Err.err.go(q, SCon{c, t}) == Err.err.esc(q, c) ++ Err.err.go(q, t)
    : String}

# LAW: a tab is written \t
# SYS-ERR-3
law esc_tab:
  for +q: Char
  {Err.err.esc(q, '\t') == "\\t" : String}

# LAW: a newline is written \n
# SYS-ERR-3
law esc_newline:
  for +q: Char
  {Err.err.esc(q, '\n') == "\\n" : String}

# LAW: a carriage return is written \r
# SYS-ERR-3
law esc_return:
  for +q: Char
  {Err.err.esc(q, '\r') == "\\r" : String}

# LAW: every other code point below U+0020, U+007F to U+00A0, and U+00AD is
# written \x and two hex digits
# SYS-ERR-3
law esc_hex:
  for +q: Char
  for +x: U32
  for set: {Bool.or(U32.is_lt(x, 32), Bool.or(Bool.and(U32.is_ge(x, 127),
    U32.is_le(x, 160)), U32.is_eq(x, 173))) == True{} : Bool}
  for tab: {U32.is_eq(x, 9) == False{} : Bool}
  for nl: {U32.is_eq(x, 10) == False{} : Bool}
  for cr: {U32.is_eq(x, 13) == False{} : Bool}
  {Err.err.esc(q, Chr{x}) == "\\x" ++ Err.err.hex2(x) : String}

# LAW: the two hex digits are lowercase, the high four bits first
# SYS-ERR-3
law hex_pair:
  for +x: U32
  {Err.err.hex2(x) == SCon{hexc(((x / 16 : U32) % 16 : U32)),
    SCon{hexc((x % 16 : U32)), SNil{}}} : String}

# LAW: a backslash is written twice
# SYS-ERR-3
law esc_backslash:
  for +q: Char
  {Err.err.esc(q, '\\') == "\\\\" : String}

# LAW: the chosen quote is written after a backslash
# SYS-ERR-3
law esc_quote:
  for +q: Char
  for +x: U32
  for set: {Bool.or(U32.is_lt(x, 32), Bool.or(Bool.and(U32.is_ge(x, 127),
    U32.is_le(x, 160)), U32.is_eq(x, 173))) == False{} : Bool}
  for bs: {U32.is_eq(x, 92) == False{} : Bool}
  for hit: {Char.is_eq(Chr{x}, q) == True{} : Bool}
  {Err.err.esc(q, Chr{x}) == SCon{'\\', SCon{q, SNil{}}} : String}

# LAW: every other character is written as itself
# SYS-ERR-3
law esc_plain:
  for +q: Char
  for +x: U32
  for set: {Bool.or(U32.is_lt(x, 32), Bool.or(Bool.and(U32.is_ge(x, 127),
    U32.is_le(x, 160)), U32.is_eq(x, 173))) == False{} : Bool}
  for bs: {U32.is_eq(x, 92) == False{} : Bool}
  for miss: {Char.is_eq(Chr{x}, q) == False{} : Bool}
  {Err.err.esc(q, Chr{x}) == SCon{Chr{x}, SNil{}} : String}
