import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope
import Definitions.Def_IPProximity_Eisenbrand_ipFeasible
import Definitions.Def_IPProximity_Eisenbrand_IsLPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsIPOptimal

namespace IPProximity.Eisenbrand

/-- Theorem 3.3 (p. 5:8): for the integer program (10) with `|aᵢⱼ| ≤ Δ`, every optimal vertex
`x` of its LP relaxation has an optimal integer solution `z` with
`‖z - x‖₁ ≤ m·(2mΔ + 1)ᵐ`, provided (10) has an integer feasible point. -/
theorem l1_proximity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (Δ : ℕ) (hΔ : ∀ i j, |A i j| ≤ (Δ : ℤ))
    (x : Fin n → ℝ) (hopt : IsLPOptimal A b c u x)
    (hvert : x ∈ Set.extremePoints ℝ (lpPolytope A b u))
    (hfeas : (ipFeasible A b u).Nonempty) :
    ∃ z : Fin n → ℤ, IsIPOptimal A b c u z ∧
      ∑ i, |(z i : ℝ) - x i| ≤ (m : ℝ) * (2 * m * Δ + 1) ^ m := by sorry

end IPProximity.Eisenbrand

