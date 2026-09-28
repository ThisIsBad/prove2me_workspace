import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope

namespace IPProximity.Eisenbrand

/-- `x` is an optimal solution of the linear programming relaxation
`max {cᵀx : A x = b, 0 ≤ x ≤ u, x ∈ ℝⁿ}` of the integer program (10) (a maximization). -/
def IsLPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ)
    (u : Fin n → ℕ) (x : Fin n → ℝ) : Prop :=
  x ∈ lpPolytope A b u ∧
    ∀ y ∈ lpPolytope A b u, dotProduct (fun i => (c i : ℝ)) y ≤ dotProduct (fun i => (c i : ℝ)) x

end IPProximity.Eisenbrand
