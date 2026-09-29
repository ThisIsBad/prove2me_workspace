import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

open scoped RealInnerProductSpace

/-- §2.1, property 3 of the composite gradient step (p. 4): under the standing assumptions of §2,
`Gf(x) = 0` if and only if `x` minimizes `f = g + h`. -/
theorem compGradStep_eq_zero_iff {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (hg : ContDiff ℝ 1 g) (hgconv : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hlip : ∀ x y, ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hh : IsProperClosedConvex D h) (x : EuclideanSpace ℝ (Fin n)) :
    compGradStep g D h 1 x = 0 ↔ IsMinimizer g D h x := by sorry

end ProxNewton.Inexact
