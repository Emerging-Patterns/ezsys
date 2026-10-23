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
