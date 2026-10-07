import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_OnlineNewtonStep
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder



namespace OnlineConvexOpt.SecondOrder

/-- Theorem 4.5 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 63, PDF p. 85). Online Newton step (Algorithm 12) on `α`-exp-concave
cost functions `f`, `G`-gradient-bounded, over a decision set `K` of diameter `D` in
`n`-dimensional space, run with `γ = (1/2) min{1/(GD), α}`, `ε = 1/(γ²D²)`, guarantees for
every `T ≥ 4`, `Regret_T ≤ 2(1/α + GD) n log T`. (The book's own derivation, immediately
following the proof, states the bound "for `n > 1`, `T ≥ 4`"; `hn : 2 ≤ n` records that
literally.)

Corrected version: `RegretT` is now the `OnlineConvexOpt_FirstOrder_Protocol_v2` regret
(genuine infimum over `K`; the retired one returned the junk value `0` outside `K`). Under the
hypotheses the cumulative cost is bounded below on `K` (convexity at the played point `x_0 ∈ K`
plus the gradient and diameter bounds), so the infimum is the book's `min`; `K` is nonempty
since `x 0 ∈ K`. -/
theorem online_newton_step_regret_v2 (n : ℕ) (hn : 2 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (α D G : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ t, ∀ p ∈ K, ∀ v, HasGradientAt (f t) v p → ‖v‖ ≤ G)
    (hα : 0 < α) (hGpos : 0 < G) (hDpos : 0 < D)
    (γ ε : ℝ) (hγ : γ = (1 / 2) * min (1 / (G * D)) α) (hε : ε = 1 / (γ ^ 2 * D ^ 2))
    (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hONS : IsOnlineNewtonStep K γ ε f x g A)
    (T : ℕ) (hT : 4 ≤ T) :
    RegretT K f x T ≤ 2 * (1 / α + G * D) * n * Real.log T := by sorry

end OnlineConvexOpt.SecondOrder

