import Mathlib
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_Extension
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.OnlineBoosting

/-- Lemma 12.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 199, PDF p. 221). The `(K,κ,δ)`-extension of a function `f̂ = X[f]`
satisfies: (1) for every `x ∈ K`, `|f̂(x) - f(x)| ≤ δG`; (2) for `κ = G`, the projection of a
point (whose gradient is bounded by `G`) onto `K` improves the extension's value up to `δG`:
`f̂(Π_K(x)) ≤ f̂(x) + δG`. -/
theorem extension_approximation_and_monotonicity
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (G δ : ℝ) (hGpos : 0 < G) (hδpos : 0 < δ)
    (hfG : ∀ x, ∀ v, HasGradientAt f v x → ‖v‖ ≤ G) :
    (∀ x ∈ K, |Extension K G δ f x - f x| ≤ δ * G) ∧
    (∀ x xπ : EuclideanSpace ℝ (Fin n), IsMetricProjection K x xπ →
      Extension K G δ f xπ ≤ Extension K G δ f x + δ * G) := by sorry

end OnlineConvexOpt.OnlineBoosting
