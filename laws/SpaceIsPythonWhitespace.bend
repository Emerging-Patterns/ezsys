# For every code point `x`, `text.space` holds of it exactly when `x` is one
# of Python's whitespace code points listed below.
#
# src/str.bend's text helpers are the ones Python's `str` gives a service for
# free, and each guarantee names the Python behaviour it matches. They work on
# code points, one at a time, left to right. Base already has
# `String.starts_with`, `String.ends_with` and `String.contains`, so ezsys
# does not add them.
#
# Python's whitespace is what `str.isspace` accepts and `str.strip()` with no
# argument removes (Unicode 13, Python 3.10): U+0009 to U+000D, U+001C to
# U+0020, U+0085, U+00A0, U+1680, U+2000 to U+200A, U+2028, U+2029, U+202F,
# U+205F and U+3000. Base's `String.trim` removes only U+0009 to U+000D and
# U+0020, and so keeps a no-break space. U+200B and U+FEFF are not whitespace,
# for Python nor here.
import Base
import ../src/str.bend as Str

# --- whitespace ---

# LAW: a character is whitespace exactly when its code point is one of
# Python's: 9 to 13, 28 to 32, 133, 160, 5760, 8192 to 8202, 8232, 8233,
# 8239, 8287 and 12288
law space_set:
  for x: U32
  {Str.text.space(Chr{x}) == List.contains(~U32, ~U32.is_eq,
    [9, 10, 11, 12, 13, 28, 29, 30, 31, 32, 133, 160, 5760, 8192, 8193, 8194,
      8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8232, 8233, 8239, 8287,
      12288], x) : Bool}
