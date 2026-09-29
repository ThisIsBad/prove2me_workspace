import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

namespace CubicNewton.LocalQuad

/-- Nesterov–Polyak 2006, Lemma 3, (2.9), p. 183, in the case `F = ℝⁿ` (so the hypothesis
`T_M(x) ∈ F` holds automatically): for every global minimizer `T = T_M(x)` of the cubic model
with `M > 0`, `‖f′(T)‖ ≤ ½(L + M) r_M(x)²` where `r_M(x) = ‖x − T‖`. -/
theorem grad_norm_at_step {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    ‖g T‖ ≤ 1 / 2 * (L + M) * ‖x - T‖ ^ 2 := by sorry

end CubicNewton.LocalQuad
