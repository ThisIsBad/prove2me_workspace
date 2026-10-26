import Mathlib
import Definitions.Def_TruncNewton_NegCurv_Setting

namespace TruncNewton.NegCurv

theorem theorem_2_4 {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (g : EuclideanSpace ℝ (Fin n))
    (hnpd : ¬ ∀ v, v ≠ 0 → 0 < inner ℝ v (H v)) :
    (∃ i, ExitsVia21 H g 0 0 i) ∨
      (∀ μ : ℝ, μ ≤ 0 → ∀ v, H v = μ • v → inner ℝ g v = 0) := by sorry

end TruncNewton.NegCurv

