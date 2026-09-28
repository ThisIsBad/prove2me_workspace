import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_IsLPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsIPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsCycle

namespace IPProximity.Eisenbrand

/-- Lemma 3.2 (p. 5:8), with the implicit `y ≠ 0`: if `x` is LP-optimal and `z` is an optimal
integer solution of (10) minimizing `‖z - x‖₁` among optimal integer solutions, then `z - x` has
no nonzero cycle. -/
theorem no_nonzero_cycle {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (x : Fin n → ℝ) (z : Fin n → ℤ)
    (hx : IsLPOptimal A b c u x) (hz : IsIPOptimal A b c u z)
    (hmin : ∀ z' : Fin n → ℤ, IsIPOptimal A b c u z' →
      ∑ i, |(z i : ℝ) - x i| ≤ ∑ i, |(z' i : ℝ) - x i|) :
    ¬ ∃ y : Fin n → ℤ, y ≠ 0 ∧ IsCycle A z x y := by sorry

end IPProximity.Eisenbrand
