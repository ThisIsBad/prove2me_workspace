import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

/-- Lemma 2.2: if `∇g` is Lipschitz continuous with constant `L1`, then
`‖Gf(x)‖ ≤ (L1 + 1) ‖x - x⋆‖` for every `x`. -/
theorem compGradStep_norm_le {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hg : ContDiff ℝ 1 g) (hgconv : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hlip : ∀ x y, ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hh : IsProperClosedConvex D h) (hxstar : IsMinimizer g D h xstar)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖compGradStep g D h 1 x‖ ≤ (L1 + 1) * ‖x - xstar‖ := by sorry

end ProxNewton.Inexact
