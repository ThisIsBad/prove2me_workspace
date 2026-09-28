import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_AggregateFunction

namespace OnlineConvexOpt.ProjectionFree

/-- Theorem 7.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 133, PDF p. 155). Online conditional gradient (Algorithm 27) with
parameters `η = D/(2GT^{3/4})`, `σ_t = min{1, 2/√t}` attains
`Regret_T = Σ_{t=1}^T f_t(x_t) - min_{x⋆∈K} Σ_{t=1}^T f_t(x⋆) ≤ 8DGT^{3/4}`.

`K` (convex, nonempty, diameter `≤ D`) and the costs `f`, convex and `G`-Lipschitz on `K`, are the
chapter-wide standing hypotheses of §7.5, stated here as explicit hypotheses — convexity of each
`f t` is used by the proof's reduction (PDF 155–156) to Theorem 5.2 applied to the shifted
sequence `f̃_t = f_t(x + (x⋆_t - x_t))`, which needs `f_t` convex for `f̃_t` to be convex.
`min_{x⋆∈K}` is rendered as an infimum. -/
theorem ocg_regret
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (G : ℝ) (hGpos : 0 < G)
    (f : ℕ → E → ℝ) (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (gradf : ℕ → E) (x1 : E) (hx1 : x1 ∈ K)
    (T : ℕ) (hT : 1 ≤ T)
    (η : ℝ) (hη : η = D / (2 * G * (T : ℝ) ^ (3 / 4 : ℝ)))
    (σ : ℕ → ℝ) (hσ : ∀ t : ℕ, 1 ≤ t → σ t = min 1 (2 / Real.sqrt t))
    (x v : ℕ → E) (hrun : IsOnlineConditionalGradientRun K f gradf x1 η σ x v) :
    (∑ t ∈ Finset.Icc 1 T, f t (x t)) - ⨅ xstar ∈ K, ∑ t ∈ Finset.Icc 1 T, f t xstar ≤
      8 * D * G * (T : ℝ) ^ (3 / 4 : ℝ) := by sorry

end OnlineConvexOpt.ProjectionFree

