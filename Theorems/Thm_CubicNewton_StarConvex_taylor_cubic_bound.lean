import Mathlib

open scoped RealInnerProductSpace

namespace CubicNewton.StarConvex

/-- Nesterov–Polyak 2006, Lemma 1, inequality (2.3), p. 181: under the standing assumptions of
Section 2 (F closed, convex, with nonempty interior; f twice differentiable on F with gradient `g`
and Hessian `H`; Assumption 1, the Hessian is `L`-Lipschitz on F), for any `x, y ∈ F`,
`|f(y) − f(x) − ⟨f′(x), y − x⟩ − ½⟨f″(x)(y − x), y − x⟩| ≤ (L/6)‖y − x‖³`. -/
theorem taylor_cubic_bound {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖) :
    ∀ x ∈ F, ∀ y ∈ F,
      |f y - f x - ⟪g x, y - x⟫ - (1 / 2) * ⟪H x (y - x), y - x⟫| ≤ L / 6 * ‖y - x‖ ^ 3 := by sorry

end CubicNewton.StarConvex

