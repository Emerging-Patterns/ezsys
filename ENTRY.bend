# ezsys: laws on the entry, main.bend. Its pure names are thin wrappers over
# src/clock.bend and src/text.bend, which LAWS.bend states the laws for.
#
# main.bend reaches src/sys.bend, whose effects are user foreign code, so from
# bend 2.0.32 no file importing it can print ALL PROOFS CHECK: the verdict
# covers every def of every import. `bend ENTRY.bend` must print
# SOME PROOFS FAIL with the foreign-code list as its only error (the effects
# and the defs that reach them); the flake's entry check holds it to that.
import Base
import ./src/clock.bend as Clock
import ./src/text.bend as Text
import ./src/str.bend as Str
import ./src/errno.bend as Err
import ./main.bend as Ez

# LAW: time.iso is src/clock.bend's
law time_iso_is_clock:
  for secs: U32
  for ms: U32
  {Ez.time.iso(secs, ms) == Clock.time.iso(secs, ms) : String}

# LAW: text.fill is src/text.bend's, over the caller's pairs in their order
law text_fill_is_text:
  for t: String
  for pairs: List<(String & String)>
  {Ez.text.fill(t, pairs) == Text.text.fill(t, Text.text.own(pairs)) : String}

# LAW: text.fill_with is src/text.bend's, over the caller's pairs in their
# order
law text_fill_with_is_text:
  for open: String
  for close: String
  for t: String
  for pairs: List<(String & String)>
  {Ez.text.fill_with(open, close, t, pairs)
    == Text.text.fill_with(open, close, t, Text.text.own(pairs)) : String}

# LAW: text.strip is src/str.bend's
law text_strip_is_str:
  for txt: String
  {Ez.text.strip(txt) == Str.text.strip(txt) : String}

# LAW: text.lstrip is src/str.bend's
law text_lstrip_is_str:
  for txt: String
  {Ez.text.lstrip(txt) == Str.text.lstrip(txt) : String}

# LAW: text.rstrip is src/str.bend's
law text_rstrip_is_str:
  for txt: String
  {Ez.text.rstrip(txt) == Str.text.rstrip(txt) : String}

# LAW: text.replace is src/str.bend's
law text_replace_is_str:
  for txt: String
  for old: String
  for new: String
  {Ez.text.replace(txt, old, new) == Str.text.replace(txt, old, new) : String}

# LAW: text.split is src/str.bend's
law text_split_is_str:
  for txt: String
  for sep: String
  {Ez.text.split(txt, sep) == Str.text.split(txt, sep) : List<&2, String>}

# LAW: text.find is src/str.bend's
law text_find_is_str:
  for txt: String
  for needle: String
  {Ez.text.find(txt, needle) == Str.text.find(txt, needle) : Maybe<&2, U32>}

# LAW: text.lower is src/str.bend's
law text_lower_is_str:
  for txt: String
  {Ez.text.lower(txt) == Str.text.lower(txt) : String}

# LAW: text.upper is src/str.bend's
law text_upper_is_str:
  for txt: String
  {Ez.text.upper(txt) == Str.text.upper(txt) : String}

# LAW: text.pad_right is src/str.bend's
law text_pad_right_is_str:
  for txt: String
  for width: Nat
  {Ez.text.pad_right(txt, width) == Str.text.pad_right(txt, width) : String}

# LAW: text.truncate is src/str.bend's
law text_truncate_is_str:
  for txt: String
  for width: Nat
  {Ez.text.truncate(txt, width) == Str.text.truncate(txt, width) : String}

# LAW: digits.cmp is src/str.bend's
law digits_cmp_is_str:
  for lhs: String
  for rhs: String
  {Ez.digits.cmp(lhs, rhs) == Str.text.digits.cmp(lhs, rhs) : Cmp}

# LAW: time.civil is src/clock.bend's fields
law time_civil_is_clock:
  for secs: U32
  {Ez.time.civil(secs) == Clock.time.fields(secs)
    : U32 & U32 & U32 & U32 & U32 & U32 & U32}

# LAW: time.iso_week is src/clock.bend's
law time_iso_week_is_clock:
  for secs: U32
  {Ez.time.iso_week(secs) == Clock.time.iso_week(secs) : U32 & U32}

# LAW: time.iso_week_text is src/clock.bend's
law time_iso_week_text_is_clock:
  for secs: U32
  {Ez.time.iso_week_text(secs) == Clock.time.iso_week_text(secs) : String}

# --- fills ---

# time_iso_is_clock holds by unfolding the re-export
def time_iso_is_clock(_secs, _ms):
  {==}

# text_fill_is_text holds by unfolding the re-export
def text_fill_is_text(_t, _pairs):
  {==}

# text_fill_with_is_text holds by unfolding the re-export
def text_fill_with_is_text(_open, _close, _t, _pairs):
  {==}

# --- errors ---

# LAW: err.os is src/errno.bend's
law err_os_is_errno:
  for code: U32
  for why: String
  for path: String
  {Ez.err.os(code, why, path) == Err.err.os(code, why, path) : String}

# err_os_is_errno holds by unfolding the re-export
def err_os_is_errno(_code, _why, _path):
  {==}

# text_strip_is_str holds by unfolding the re-export
def text_strip_is_str(_txt):
  {==}

# text_lstrip_is_str holds by unfolding the re-export
def text_lstrip_is_str(_txt):
  {==}

# text_rstrip_is_str holds by unfolding the re-export
def text_rstrip_is_str(_txt):
  {==}

# text_replace_is_str holds by unfolding the re-export
def text_replace_is_str(_txt, _old, _new):
  {==}

# text_split_is_str holds by unfolding the re-export
def text_split_is_str(_txt, _sep):
  {==}

# text_find_is_str holds by unfolding the re-export
def text_find_is_str(_txt, _needle):
  {==}

# text_lower_is_str holds by unfolding the re-export
def text_lower_is_str(_txt):
  {==}

# text_upper_is_str holds by unfolding the re-export
def text_upper_is_str(_txt):
  {==}

# text_pad_right_is_str holds by unfolding the re-export
def text_pad_right_is_str(_txt, _width):
  {==}

# text_truncate_is_str holds by unfolding the re-export
def text_truncate_is_str(_txt, _width):
  {==}

# digits_cmp_is_str holds by unfolding the re-export
def digits_cmp_is_str(_lhs, _rhs):
  {==}

# time_civil_is_clock holds by unfolding the re-export
def time_civil_is_clock(_secs):
  {==}

# time_iso_week_is_clock holds by unfolding the re-export
def time_iso_week_is_clock(_secs):
  {==}

# time_iso_week_text_is_clock holds by unfolding the re-export
def time_iso_week_text_is_clock(_secs):
  {==}
