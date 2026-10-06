import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum

open scoped RealInnerProductSpace

namespace SAGA.Convex

/-- Lemma 1 (= Lemma 5), pp. 6–7 and 10: for `f = (1/n) ∑ fᵢ` with each `fᵢ` `μ`-strongly convex
(`μ ≥ 0`; `μ = 0` is plain convexity, the case used for Theorem 2) and with `L`-Lipschitz
gradients, for all `x` and `x*`,
`⟨f′(x), x* - x⟩ ≤ ((L - μ)/L)[f(x*) - f(x)] - (μ/2)‖x* - x‖²
  - (1/(2Ln)) ∑ᵢ ‖f′ᵢ(x*) - f′ᵢ(x)‖² - (μ/L)⟨f′(x*), x - x*⟩`. -/
theorem lemma1_inner_bound {d n : ℕ} (hn : 0 < n) {L μ : ℝ} (hL : 0 < L) (hμ : 0 ≤ μ)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, StrongConvexOn Set.univ μ (f i))
    (x xs : EuclideanSpace ℝ (Fin d)) :
    ⟪gradAvg f' x, xs - x⟫ ≤
      (L - μ) / L * (fAvg f xs - fAvg f x) - μ / 2 * ‖xs - x‖ ^ 2
        - 1 / (2 * L * n) * ∑ i, ‖f' i xs - f' i x‖ ^ 2
        - μ / L * ⟪gradAvg f' xs, x - xs⟫ := by sorry

end SAGA.Convex

