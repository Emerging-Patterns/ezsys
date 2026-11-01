# For every path, `repr` writes the quote, each character of the path escaped
# as stated above, and the quote; the quote is `"` exactly when the path holds
# a `'` and no `"`.
import Base
import ../src/errno.bend as Err

# the hex digit at a place of "0123456789abcdef", '0' past it
def hexc(place: U32) -> Char:
  Err.err.hex.or(String.get("0123456789abcdef", U32.to_nat(place)))

# LAW: repr is the quote, the escaped characters and the quote
law repr_shape:
  for +path: String
  {Err.err.repr(path) == SCon{Err.err.quote(path),
    Err.err.go(Err.err.quote(path), path)
      ++ SCon{Err.err.quote(path), SNil{}}} : String}

# LAW: a path with a ' and no " is quoted with "
law quote_double:
  for +path: String
  for one: {String.contains(path, "'") == True{} : Bool}
  for two: {String.contains(path, "\"") == False{} : Bool}
  {Err.err.quote(path) == '"' : Char}

# LAW: a path with no ' is quoted with '
law quote_plain:
  for +path: String
  for e: {String.contains(path, "'") == False{} : Bool}
  {Err.err.quote(path) == '\'' : Char}

# LAW: a path with a " is quoted with '
law quote_both:
  for +path: String
  for e: {String.contains(path, "\"") == True{} : Bool}
  {Err.err.quote(path) == '\'' : Char}

# LAW: no characters are written as nothing
law go_empty:
  for +q: Char
  {Err.err.go(q, "") == "" : String}

# LAW: the characters are escaped one by one, in order
law go_char:
  for +q: Char
  for c: Char
  for t: String
  {Err.err.go(q, SCon{c, t}) == Err.err.esc(q, c) ++ Err.err.go(q, t)
    : String}

# LAW: a tab is written \t
law esc_tab:
  for +q: Char
  {Err.err.esc(q, '\t') == "\\t" : String}

# LAW: a newline is written \n
law esc_newline:
  for +q: Char
  {Err.err.esc(q, '\n') == "\\n" : String}

# LAW: a carriage return is written \r
law esc_return:
  for +q: Char
  {Err.err.esc(q, '\r') == "\\r" : String}

# LAW: every other code point below U+0020, U+007F to U+00A0, and U+00AD is
# written \x and two hex digits
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
law hex_pair:
  for +x: U32
  {Err.err.hex2(x) == SCon{hexc(((x / 16 : U32) % 16 : U32)),
    SCon{hexc((x % 16 : U32)), SNil{}}} : String}

# LAW: a backslash is written twice
law esc_backslash:
  for +q: Char
  {Err.err.esc(q, '\\') == "\\\\" : String}

# LAW: the chosen quote is written after a backslash
law esc_quote:
  for +q: Char
  for +x: U32
  for set: {Bool.or(U32.is_lt(x, 32), Bool.or(Bool.and(U32.is_ge(x, 127),
    U32.is_le(x, 160)), U32.is_eq(x, 173))) == False{} : Bool}
  for bs: {U32.is_eq(x, 92) == False{} : Bool}
  for hit: {Char.is_eq(Chr{x}, q) == True{} : Bool}
  {Err.err.esc(q, Chr{x}) == SCon{'\\', SCon{q, SNil{}}} : String}

# LAW: every other character is written as itself
law esc_plain:
  for +q: Char
  for +x: U32
  for set: {Bool.or(U32.is_lt(x, 32), Bool.or(Bool.and(U32.is_ge(x, 127),
    U32.is_le(x, 160)), U32.is_eq(x, 173))) == False{} : Bool}
  for bs: {U32.is_eq(x, 92) == False{} : Bool}
  for miss: {Char.is_eq(Chr{x}, q) == False{} : Bool}
  {Err.err.esc(q, Chr{x}) == SCon{Chr{x}, SNil{}} : String}
