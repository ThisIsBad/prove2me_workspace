import Mathlib

open scoped InnerProductSpace

namespace SAGA.StronglyConvex

/-- Lemma 4 (Appendix B, p. 10). `f` is `μ`-strongly convex with `L`-Lipschitz gradient `f'`.
The page leaves `μ < L` implicit; the fractions `1/(L-μ)` require it, so it is a hypothesis. -/
theorem lemma4_strongly_convex_smooth_lower_bound {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (f' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ L : ℝ) (hμ : 0 < μ) (hμL : μ < L)
    (hgrad : ∀ x, HasGradientAt f (f' x) x)
    (hsc : StrongConvexOn Set.univ μ f)
    (hlip : ∀ x y, ‖f' x - f' y‖ ≤ L * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin d)) :
    f y + ⟪f' y, x - y⟫_ℝ + 1 / (2 * (L - μ)) * ‖f' x - f' y‖ ^ 2
      + μ * L / (2 * (L - μ)) * ‖y - x‖ ^ 2 + μ / (L - μ) * ⟪f' x - f' y, y - x⟫_ℝ ≤ f x := by sorry

end SAGA.StronglyConvex

