import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope
import Definitions.Def_IPProximity_Eisenbrand_IsLPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsIPOptimal

namespace IPProximity.Eisenbrand

/-- Eq. (21) (p. 5:9): the absolute integrality gap of (10) at an optimal LP vertex `x` is at
most `‖c‖∞·m·(2mΔ + 1)ᵐ`, for every optimal integer solution `z`. The norm of the real vector
`(cᵢ)ᵢ` below is Mathlib's sup norm on `Fin n → ℝ`, i.e. `‖c‖∞`. -/
theorem integrality_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (Δ : ℕ) (hΔ : ∀ i j, |A i j| ≤ (Δ : ℤ))
    (x : Fin n → ℝ) (hopt : IsLPOptimal A b c u x)
    (hvert : x ∈ Set.extremePoints ℝ (lpPolytope A b u))
    (z : Fin n → ℤ) (hz : IsIPOptimal A b c u z) :
    dotProduct (fun i => (c i : ℝ)) x - dotProduct (fun i => (c i : ℝ)) (fun i => (z i : ℝ)) ≤
      ‖(fun i => (c i : ℝ))‖ * ((m : ℝ) * (2 * m * Δ + 1) ^ m) := by sorry

end IPProximity.Eisenbrand

