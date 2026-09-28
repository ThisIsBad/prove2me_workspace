import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope
import Definitions.Def_IPProximity_Eisenbrand_ipFeasible
import Definitions.Def_IPProximity_Eisenbrand_IsLPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsIPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsCycle

namespace IPProximity.Eisenbrand

/-- Lemma 3.1 (p. 5:8): if `x` is LP-optimal, `z` is IP-optimal for (10) and `y` is a cycle of
`z - x`, then (i) `z - y` is integer feasible, (ii) `x + y` is LP feasible, (iii) `cᵀy ≤ 0`. -/
theorem cycle_exchange {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (x : Fin n → ℝ) (z : Fin n → ℤ)
    (hx : IsLPOptimal A b c u x) (hz : IsIPOptimal A b c u z)
    (y : Fin n → ℤ) (hy : IsCycle A z x y) :
    z - y ∈ ipFeasible A b u ∧
      (x + fun i => (y i : ℝ)) ∈ lpPolytope A b u ∧
      dotProduct c y ≤ 0 := by sorry

end IPProximity.Eisenbrand
