import Mathlib
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_Extension
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open OnlineConvexOpt.FirstOrder



namespace OnlineConvexOpt.OnlineBoosting

/-- Lemma 12.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 199, PDF p. 221), corrected constants. For a convex, `G`-Lipschitz loss
`f : ℝⁿ → ℝ` (the chapter's standing assumptions: losses are convex, defined over all of `ℝⁿ`,
with (sub)gradients bounded by `G`, p. 198) and a nonempty convex `K`, the `(K,G,δ)`-extension
`f̂ = X_{K,G,δ}[f]` satisfies: (1) for every `x ∈ K`, `|f̂(x) - f(x)| ≤ 2δG`; (2) the projection
of any point onto `K` improves the extension's value up to `2δG`: `f̂(Π_K(x)) ≤ f̂(x) + 2δG`.

Corrected version. (i) The retired statement tied `f` to `G` only through a gradient bound at
points of differentiability, which is vacuous for discontinuous `f`; the hypothesis is now the
`G`-Lipschitz condition that Lemma 2.8 (which the proof invokes) needs, together with convexity
of `f`, used in part (2) (`S_δ[f + G·Dist(·,K)](x) ≥ f(x) + G·Dist(x,K)` by Jensen). (ii) The
printed constant `δG` is corrected to `2δG`: the smoothing ball around `x ∈ K` leaves `K`, where
the penalty `G·Dist(·,K)` contributes up to `δG` on top of Lemma 2.8's `δG` (for `K = {0}`,
`f = G‖·‖` in dimension `n ≥ 2` one has `f̂(0) - f(0) = 2δG·n/(n+1) > δG`), and part (2) inherits
the same constant. -/
theorem extension_approximation_and_monotonicity_v2
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfconv : ConvexOn ℝ Set.univ f)
    (G δ : ℝ) (hGpos : 0 < G) (hδpos : 0 < δ)
    (hfG : ∀ x y, |f x - f y| ≤ G * dist x y) :
    (∀ x ∈ K, |Extension K G δ f x - f x| ≤ 2 * δ * G) ∧
    (∀ x xπ : EuclideanSpace ℝ (Fin n), IsMetricProjection K x xπ →
      Extension K G δ f xπ ≤ Extension K G δ f x + 2 * δ * G) := by sorry

end OnlineConvexOpt.OnlineBoosting

