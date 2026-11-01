# Bool facts: True is never False, a false any, and anything from Empty
import Base
import ../../src/text.bend as Text

# --- Bool facts ---

# Unit for True, Empty for False: tells them apart
def bit(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

# True is never False
def clash(e: {True{} == False{} : Bool}) -> Empty:
  %e : bit(_)
  Unit{}

# anything follows from Empty
def gone(a, -A: Kind(a), e: Empty) -> A:
  match e:

# a false any has a false first test
law any_false_l:
  for here: Bool
  for rest: Unit -> Bool
  for e: {Text.text.any(here, rest) == False{} : Bool}
  {here == False{} : Bool}

def any_false_l(here, _rest, e):
  match here:
    case False{}:
      {==}
    case True{}:
      gone(&1, {True{} == False{} : Bool}, clash(e))

# a false any has a false rest
law any_false_r:
  for here: Bool
  for rest: Unit -> Bool
  for e: {Text.text.any(here, rest) == False{} : Bool}
  {rest(Unit{}) == False{} : Bool}

def any_false_r(here, rest, e):
  match here:
    case False{}:
      e
    case True{}:
      gone(&1, {rest(Unit{}) == False{} : Bool}, clash(e))

# --- whitespace ---

# a false is not true
def no(-G: Type, e: {False{} == True{} : Bool}) -> G:
  gone(&1, G, clash(Equal.sym(Bool, False{}, True{}, e)))
