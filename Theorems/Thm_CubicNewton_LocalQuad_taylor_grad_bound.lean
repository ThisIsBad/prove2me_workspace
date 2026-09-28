import Mathlib

namespace CubicNewton.LocalQuad

/-- Nesterov–Polyak 2006, Lemma 1, inequality (2.2), p. 181, in the case `F = ℝⁿ`:
if `f` is twice differentiable on `ℝⁿ` with `L`-Lipschitz Hessian, then for all `x, y`,
`‖f′(y) − f′(x) − f″(x)(y − x)‖ ≤ ½ L ‖y − x‖²`. -/
theorem taylor_grad_bound {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖) :
    ∀ x y, ‖g y - g x - H x (y - x)‖ ≤ 1 / 2 * L * ‖y - x‖ ^ 2 := by sorry

end CubicNewton.LocalQuad
