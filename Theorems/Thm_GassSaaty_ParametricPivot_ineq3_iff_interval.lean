import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem ineq3_iff_interval {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ) (B : Fin m ↪ Fin n)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0) (t : ℝ) :
    (∀ j, alpha A d B j + t * beta A d' B j ≤ 0) ↔
      (lamLower A d d' B ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ lamBar A d d' B) := by sorry

end GassSaaty.ParametricPivot

