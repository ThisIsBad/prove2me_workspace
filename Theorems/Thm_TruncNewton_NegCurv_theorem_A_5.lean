import Mathlib
import Definitions.Def_TruncNewton_NegCurv_Setting

namespace TruncNewton.NegCurv

theorem theorem_A_5 {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (g : EuclideanSpace ℝ (Fin n))
    (hg : ∀ μ : ℝ, (∃ v, v ≠ 0 ∧ H v = μ • v) → ∃ v, H v = μ • v ∧ inner ℝ g v ≠ 0)
    (k : ℕ) (hk : k = Set.ncard {μ : ℝ | ∃ v, v ≠ 0 ∧ H v = μ • v})
    (d : ℕ → EuclideanSpace ℝ (Fin n))
    (hconj : ∀ i j, i < k → j < k → i ≠ j → inner ℝ (d i) (H (d j)) = 0)
    (hpos : ∀ i, i < k → 0 < inner ℝ (d i) (H (d i)))
    (hspan : Submodule.span ℝ (d '' Set.Iio k) =
      Submodule.span ℝ ((fun i => (H ^ i) g) '' Set.Iio k)) :
    ∀ v, v ≠ 0 → 0 < inner ℝ v (H v) := by sorry

end TruncNewton.NegCurv

