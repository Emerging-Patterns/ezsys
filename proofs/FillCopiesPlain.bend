# proofs of laws/FillCopiesPlain.bend
import Base
import ../src/text.bend as Text
import ../laws/FillCopiesPlain.bend as Laws

# --- the scan ---

def Laws.fill_plain(oh, ot, ch, ct, h, t, pairs, e):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, SCon{oh, ot}), False{}, e)
    : {Text.text.join(Text.text.plain(_, h, SCon{oh, ot}),
      next => Text.text.go(t, next, SCon{oh, ot}, SCon{ch, ct}, pairs))
      == SCon{h, Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, t, pairs)}
      : String}
  {==}
