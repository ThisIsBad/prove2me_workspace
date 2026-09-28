import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem

namespace JohnsonApprox.MaxSatGreedy

/-- The positive literal `x_i`. -/
def x (i : ℕ) : Shared.Literal := ⟨i, true⟩

/-- The negative literal `x̄_i`. -/
def xbar (i : ℕ) : Shared.Literal := ⟨i, false⟩

/-- The paper's `k = 3` input (p. 263):
`S = {{x_1, x_2, x_3}, {x̄_1, x_4, x_5}, {x̄_2, x_6, x_7}, {x̄_3, x_8, x_9}}`. -/
def exampleK3 : Finset Shared.Clause :=
  {{x 1, x 2, x 3}, {xbar 1, x 4, x 5}, {xbar 2, x 6, x 7}, {xbar 3, x 8, x 9}}

end JohnsonApprox.MaxSatGreedy
