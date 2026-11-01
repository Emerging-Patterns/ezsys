# proofs of laws/FirstPairGivesValue.bend
import Base
import ../src/text.bend as Text
import ../laws/FirstPairGivesValue.bend as Laws

def Laws.value_none(_key):
  {==}

def Laws.own_order(_k, _v, _rest):
  {==}

def Laws.value_hit(k, v, rest, key, e):
  %Equal.sym(Bool, String.eq(k, key), True{}, e)
    : {Text.text.value.pick(_, v, _u => Text.text.value(rest, key)) == Some{v}
      : Maybe<&2, String>}
  {==}

def Laws.value_miss(k, v, rest, key, e):
  %Equal.sym(Bool, String.eq(k, key), False{}, e)
    : {Text.text.value.pick(_, v, _u => Text.text.value(rest, key))
      == Text.text.value(rest, key) : Maybe<&2, String>}
  {==}
