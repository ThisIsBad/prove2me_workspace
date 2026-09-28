import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem

namespace JohnsonApprox.MaxSatWeighted

/-- The positive literal `x_i`. -/
def lit (i : ℕ) : Shared.Literal := ⟨i, true⟩

/-- The negative literal `x̄_i`. -/
def nlit (i : ℕ) : Shared.Literal := ⟨i, false⟩

/-- The lower-bound input for `k = 3` from the proof of Theorem 3 (p. 264):
`S = {{x_1, x_2, x_3}, {x̄_1, x_4, x_5}, {x_1, x̄_2, x_3}, {x̄_1, x_6, x_7},
{x_1, x_2, x̄_3}, {x̄_1, x_8, x_9}, {x_1, x̄_2, x̄_3}, {x̄_1, x_10, x_11}}`.
Variable `x_i` is the variable with index `i`. -/
def exampleK3 : Finset Shared.Clause :=
  {{lit 1, lit 2, lit 3}, {nlit 1, lit 4, lit 5},
   {lit 1, nlit 2, lit 3}, {nlit 1, lit 6, lit 7},
   {lit 1, lit 2, nlit 3}, {nlit 1, lit 8, lit 9},
   {lit 1, nlit 2, nlit 3}, {nlit 1, lit 10, lit 11}}

end JohnsonApprox.MaxSatWeighted
