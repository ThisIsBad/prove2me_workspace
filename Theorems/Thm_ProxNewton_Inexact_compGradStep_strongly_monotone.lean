import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

open scoped RealInnerProductSpace

/-- Lemma 3.9: under the standing assumptions of §3.4, the composite gradient step `G_t f` with
step length `0 < t ≤ 1/L1` is strongly monotone with constant `m/2`:
`(x - y)ᵀ(G_t f(x) - G_t f(y)) ≥ (m/2) ‖x - y‖²` (Eq. (3.7)). -/
theorem compGradStep_strongly_monotone {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (m L1 L2 t : ℝ)
    (hg : SmoothPartAssumptions g m L1 L2) (hh : IsProperClosedConvex D h)
    (ht : 0 < t) (htL1 : t * L1 ≤ 1) (x y : EuclideanSpace ℝ (Fin n)) :
    m / 2 * ‖x - y‖ ^ 2 ≤ ⟪x - y, compGradStep g D h t x - compGradStep g D h t y⟫ := by sorry

end ProxNewton.Inexact
