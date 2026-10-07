import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_OnlineNewtonStep
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder



namespace OnlineConvexOpt.SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma 4.6 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 63, PDF p. 85). The regret of online Newton step (Algorithm 12, run with
parameters `γ = (1/2) min{1/(GD), α}`, `ε = 1/(γ²D²)` against `α`-exp-concave cost functions `f`
with gradient bound `G` over a decision set `K` of diameter `D`) is bounded by
`Regret_T(ONS) ≤ (1/α + GD)(Σ_{t=1}^T ∇_t^⊤A_t^{-1}∇_t + 1)`, where `∇_t^⊤A_t^{-1}∇_t` is the
quadratic form `quadForm (A (t+1)).inverse (g t)` — the sum runs over the 0-indexed rounds
`t = 0, ..., T - 1`, i.e. the book's `t = 1, ..., T`, matching `A (t + 1)`'s shift in
`IsOnlineNewtonStep`.

Corrected version: `RegretT` is now the `OnlineConvexOpt_FirstOrder_Protocol_v2` regret
(genuine infimum over `K`; the retired one returned the junk value `0` outside `K`). Under the
hypotheses the cumulative cost is bounded below on `K` (convexity at the played point `x_0 ∈ K`
plus the gradient and diameter bounds), so the infimum is the book's `min`. -/
theorem online_newton_step_regret_bound_v2
    (K : Set E) (α D G γ ε : ℝ) (f : ℕ → E → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ t, ∀ p ∈ K, ∀ v, HasGradientAt (f t) v p → ‖v‖ ≤ G)
    (hα : 0 < α) (hGpos : 0 < G) (hDpos : 0 < D)
    (hγ : γ = (1 / 2) * min (1 / (G * D)) α) (hε : ε = 1 / (γ ^ 2 * D ^ 2))
    (x g : ℕ → E) (A : ℕ → E →L[ℝ] E) (hONS : IsOnlineNewtonStep K γ ε f x g A)
    (T : ℕ) :
    RegretT K f x T ≤
      (1 / α + G * D) *
        ((∑ t ∈ Finset.range T, quadForm (A (t + 1)).inverse (g t)) + 1) := by sorry

end OnlineConvexOpt.SecondOrder

