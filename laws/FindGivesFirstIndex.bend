# `text.find(s, needle)` is Python's `s.find(needle)` with `None` for its
# `-1`: the index in code points of the first place the needle starts. An
# empty needle is found at 0; for every `h` and `t`, a needle that starts at
# `h ++ t` is found at 0, and one that does not is found at `i + 1` when it is
# found at `i` in `t` and not found when it is not found in `t`; a nonempty
# needle is not found in the empty text.
import Base
import ../src/str.bend as Str

# LAW: an empty needle is found at 0
law find_empty:
  for s: String
  {Str.text.find(s, "") == Some{0} : Maybe<&2, U32>}

# LAW: a needle at the start is found at 0
law find_hit:
  for +h: Char
  for +t: String
  for +needle: String
  for e: {String.starts_with(SCon{h, t}, needle) == True{} : Bool}
  {Str.text.find(SCon{h, t}, needle) == Some{0} : Maybe<&2, U32>}

# LAW: past a character where the needle does not start, a needle found at
# i in the rest is found at i + 1
law find_next:
  for +h: Char
  for +t: String
  for +needle: String
  for i: U32
  for e: {String.starts_with(SCon{h, t}, needle) == False{} : Bool}
  for got: {Str.text.find(t, needle) == Some{i} : Maybe<&2, U32>}
  {Str.text.find(SCon{h, t}, needle) == Some{(i + 1 : U32)}
    : Maybe<&2, U32>}

# LAW: past a character where the needle does not start, a needle not in
# the rest is not found
law find_none:
  for +h: Char
  for +t: String
  for +needle: String
  for e: {String.starts_with(SCon{h, t}, needle) == False{} : Bool}
  for got: {Str.text.find(t, needle) == None{} : Maybe<&2, U32>}
  {Str.text.find(SCon{h, t}, needle) == None{} : Maybe<&2, U32>}

# LAW: a nonempty needle is not found in the empty text
law find_end:
  for nh: Char
  for nt: String
  {Str.text.find("", SCon{nh, nt}) == None{} : Maybe<&2, U32>}
