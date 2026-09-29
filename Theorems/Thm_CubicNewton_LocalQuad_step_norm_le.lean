import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep
import Definitions.Def_CubicNewton_Shared_lamMin

namespace CubicNewton.LocalQuad

/-- Nesterov–Polyak 2006, Section 3, Eq. (3.9), p. 187 (proof of Theorem 3), in the case
`F = ℝⁿ`: if `f″(x) ≻ 0` (i.e. `λₙ(f″(x)) > 0`), `M > 0` and `T = T_M(x)` is a global
minimizer of the cubic model at `x`, then `r_M(x) = ‖T − x‖ ≤ ‖f′(x)‖ / λₙ(f″(x))`. -/
theorem step_norm_le {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n))
    (hpos : 0 < CubicNewton.Shared.lamMin (H x)) (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    ‖T - x‖ ≤ ‖g x‖ / CubicNewton.Shared.lamMin (H x) := by sorry

end CubicNewton.LocalQuad
