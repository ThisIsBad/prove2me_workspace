import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The projection `R∪{±∞} → R∪{+∞}` sending `-∞` to the junk value `+∞`. -/
def FromEReal (v : EReal) : WithTop ℝ := WithBot.unbotD ⊤ v

end DiscreteConvex.AlgorithmsC
