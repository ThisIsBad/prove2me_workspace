import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_ipFeasible

namespace IPProximity.Eisenbrand

/-- `z` is an optimal solution of the integer program (10)
`max {cᵀz : A z = b, 0 ≤ z ≤ u, z ∈ ℤⁿ}` (a maximization). -/
def IsIPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ)
    (u : Fin n → ℕ) (z : Fin n → ℤ) : Prop :=
  z ∈ ipFeasible A b u ∧ ∀ z' ∈ ipFeasible A b u, dotProduct c z' ≤ dotProduct c z

end IPProximity.Eisenbrand
