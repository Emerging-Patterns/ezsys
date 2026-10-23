# ezsys/src/errno: a file operation's failure written as Python writes an
# OSError: `[Errno N] <strerror>: <repr(path)>`. The text of a code is
# glibc's, from a table of common Linux codes; a code the table does not
# list is written with the message it came with. The path is written as
# Python's repr(str) writes it, for the characters up to U+00FF.
import Base

# the codes and their texts, reusable
def err.Table() -> Data:
  List<&2, Sigma<&2, &2, U32, _ => String>>

# the common Linux codes and glibc's text for each, as os.strerror gives it
def err.table() -> err.Table():
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

# what is written when hit holds, else what the rest writes
def err.when(hit: Bool, yes: Unit -> String, no: Unit -> String) -> String:
  match hit:
    case True{}:
      yes(Unit{})
    case False{}:
      no(Unit{})

# the text of the first pair with the code, or why when there is none
def err.look(table: err.Table(), +code: U32, +why: String) -> String:
  match table:
    case Nil{}:
      why
    case Con{(k, text), rest}:
      err.when(U32.is_eq(code, k), _u => text, _u => err.look(rest, code, why))

# a code's text: the table's, or why when the table does not list it
def err.text(+code: U32, +why: String) -> String:
  err.look(err.table(), code, why)

# the quote a path is written between: " when it holds a ' and no ", else '
def err.quote.pick(dq: Bool) -> Char:
  match dq:
    case True{}:
      '"'
    case False{}:
      '\''

# the quote repr picks for a path
def err.quote(+path: String) -> Char:
  err.quote.pick(Bool.and(String.contains(path, "'"),
    Bool.not(String.contains(path, "\""))))

# the code points repr writes as \xhh: below U+0020, U+007F to U+00A0, and
# U+00AD
def err.hexed(+cp: U32) -> Bool:
  Bool.or(U32.is_lt(cp, 32),
    Bool.or(Bool.and(U32.is_ge(cp, 127), U32.is_le(cp, 160)),
      U32.is_eq(cp, 173)))

# a digit's character, or '0' past the digits
def err.hex.or(got: Maybe<&2, Char>) -> Char:
  match got:
    case None{}:
      '0'
    case Some{chr}:
      chr

# the lowercase hex digit of a number's last four bits
def err.hex.digit(num: U32) -> Char:
  err.hex.or(String.get("0123456789abcdef", U32.to_nat((num % 16 : U32))))

# two lowercase hex digits of a number's last eight bits
def err.hex2(+cp: U32) -> String:
  SCon{err.hex.digit((cp / 16 : U32)), SCon{err.hex.digit(cp), SNil{}}}

# a control character: \t, \n, \r, or \xhh
def err.ctl(+cp: U32) -> String:
  err.when(U32.is_eq(cp, 9), _u => "\\t",
    _u => err.when(U32.is_eq(cp, 10), _v => "\\n",
      _v => err.when(U32.is_eq(cp, 13), _w => "\\r",
        _w => "\\x" ++ err.hex2(cp))))

# any other character: a backslash or the quote escaped, else itself
def err.plain(+qt: Char, +cp: U32) -> String:
  err.when(U32.is_eq(cp, 92), _u => "\\\\",
    _u => err.when(Char.is_eq(Chr{cp}, qt), _v => SCon{'\\', SCon{qt, SNil{}}},
      _v => SCon{Chr{cp}, SNil{}}))

# one character of a path between the quote q
def err.esc(+qt: Char, chr: Char) -> String:
  match chr:
    case Chr{+cp}:
      err.when(err.hexed(cp), _u => err.ctl(cp), _u => err.plain(qt, cp))

# a path's characters between the quote q
def err.go(+qt: Char, path: String) -> String:
  match path:
    case SNil{}:
      SNil{}
    case SCon{chr, t}:
      err.esc(qt, chr) ++ err.go(qt, t)

# a path as Python's repr(str) writes it
def err.repr(+path: String) -> String:
  +qt = err.quote(path)
  SCon{qt, err.go(qt, path) ++ SCon{qt, SNil{}}}

# a failed file operation as Python's OSError writes it
def err.os(+code: U32, +why: String, +path: String) -> String:
  "[Errno " ++ U32.show(code) ++ "] " ++ err.text(code, why) ++ ": "
    ++ err.repr(path)
