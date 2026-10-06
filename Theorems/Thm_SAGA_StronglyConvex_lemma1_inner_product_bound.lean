import Mathlib

open scoped InnerProductSpace

namespace SAGA.StronglyConvex

/-- Lemma 1 (pp. 6–7, = Lemma 5, p. 10). `f = (1/n) Σ_i f_i`, each `f_i` `μ`-strongly convex with
`L`-Lipschitz gradient `f'_i`; `f' = (1/n) Σ_i f'_i`. The points `x` and `x*` (here `xs`) are
arbitrary. -/
theorem lemma1_inner_product_bound {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ L : ℝ) (hμ : 0 < μ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hsc : ∀ i, StrongConvexOn Set.univ μ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (x xs : EuclideanSpace ℝ (Fin d)) :
    ⟪(1 / (n : ℝ)) • ∑ i, f' i x, xs - x⟫_ℝ ≤
      (L - μ) / L * ((1 / (n : ℝ)) * ∑ i, f i xs - (1 / (n : ℝ)) * ∑ i, f i x)
        - μ / 2 * ‖xs - x‖ ^ 2
        - 1 / (2 * L * n) * ∑ i, ‖f' i xs - f' i x‖ ^ 2
        - μ / L * ⟪(1 / (n : ℝ)) • ∑ i, f' i xs, x - xs⟫_ℝ := by sorry

end SAGA.StronglyConvex

