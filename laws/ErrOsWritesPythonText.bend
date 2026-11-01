# For every code, `why` and path, `err.os(code, why, path)` is exactly `[Errno
# `, the code in decimal, `] `, the code's text, `: ` and the path as `repr`
# writes it.
#
# `err.os(code, why, path)` writes a failed file operation's `Fail{(code,
# why)}` the way Python's `OSError.__str__` writes an error with a file name:
# `[Errno N] <strerror>: <repr(path)>`, as in `[Errno 2] No such file or
# directory: '/tmp/x'`. The text of a code is glibc's, as Python's
# `os.strerror` gives it on Linux, for the codes 1 to 40 and 84 (`EILSEQ`), 95
# (`EOPNOTSUPP`), 110 (`ETIMEDOUT`), 111 (`ECONNREFUSED`), 112 (`EHOSTDOWN`),
# 113 (`EHOSTUNREACH`), 116 (`ESTALE`), 122 (`EDQUOT`) and 125 (`ECANCELED`);
# `strerror` in laws/StrerrorTableLookup.bend lists them. For any other code
# `why` is written as it came, where Python writes glibc's text for the code
# or `Unknown error N`.
#
# The path is written as Python's `repr(str)` writes it for every code point
# up to U+00FF (laws/ReprQuotesAndEscapes.bend): between `"` when it holds a
# `'` and no `"`, else between `'`; `\t`, `\n` and `\r` for those characters;
# `\xhh` (two lowercase hex digits) for every other code point below U+0020,
# from U+007F to U+00A0, and U+00AD; a backslash before a backslash and before
# the chosen quote; every other character as itself. Python also writes
# `\xhh`, `\uhhhh` or `\Uhhhhhhhh` for the code points past U+00FF that
# `str.isprintable` rejects (U+2028, U+200B, U+FEFF and the like); those are
# written as themselves here, which is outside this guarantee.
import Base
import ../src/errno.bend as Err

# LAW: [Errno N] text: repr(path)
law err_os:
  for +code: U32
  for +why: String
  for +path: String
  {Err.err.os(code, why, path) == "[Errno " ++ U32.show(code) ++ "] "
    ++ Err.err.text(code, why) ++ ": " ++ Err.err.repr(path) : String}
