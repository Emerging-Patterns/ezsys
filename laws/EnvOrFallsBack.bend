# For every name and fallback, `env.or(name, fallback)` answers the variable's
# value when it is set, even when that value is empty, and exactly `fallback`
# when it is not.
import Base
import ../src/step.bend as Step

# --- environment ---

# LAW: a set variable's value is the answer, even an empty one
law env_set:
  for value: String
  for fallback: String
  {Step.env.pick(Done{value}, fallback) == value : String}

# LAW: an unset variable answers the fallback
law env_unset:
  for code: U32
  for why: String
  for fallback: String
  {Step.env.pick(Fail{(code, why)}, fallback) == fallback : String}
