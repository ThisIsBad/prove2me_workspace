import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_ConditionalGradient
import Definitions.Def_OnlineConvexOpt_ProjectionFree_SmoothOn



namespace OnlineConvexOpt.ProjectionFree

/-- Theorem 7.1 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 127, PDF p. 149). The (offline) conditional gradient algorithm
(Algorithm 25) applied to `β`-smooth convex functions with step sizes `η_t = min{1, 2/t}`
attains `h_t ≤ 2βD²/t` for every `t ≥ 2`, where `h_t = f(x_t) - f(x⋆)` and `D` is the
diameter of `K`.

`K` (convex, nonempty, diameter `≤ D`), `f` (convex and `β`-smooth on `K` with gradient map `g`,
§7.3's own setup, "minimizing a smooth convex function `f` over a convex set `K`", p. 126), and
`x⋆` (a global minimizer of `f` over `K`) are the chapter's standing hypotheses for this
theorem, stated explicitly.

Corrected version. (i) The range is `t ≥ 2`: the printed statement gives no range, but its
proof (Lemma 7.2) only establishes the recursion from `h_2 ≤ βD²/2` on, and at `t = 1` the
claim `h_1 ≤ 2βD²` is false (nothing bounds the suboptimality of an arbitrary starting point
`x_1 ∈ K`, e.g. a steep linear `f`). (ii) `g` is required to be the gradient of `f` at the
points of `K` (`hg`), as in the book where `∇f` is the gradient: the retired statement tied `g`
to `f` only through the smoothness inequality, which does not force `g(x)` to be a subgradient
at boundary points of `K`, and the proof's convexity step `f(x⋆) ≥ f(x_t) + ⟪g(x_t), x⋆ - x_t⟫`
then fails (a run can stall at a non-optimal point). -/
theorem cg_convergence_v2
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (f : E → ℝ) (g : E → E) (hg : ∀ x ∈ K, HasGradientAt f (g x) x)
    (β : ℝ) (hβpos : 0 < β) (hsmooth : SmoothOn K f g β)
    (hfconv : ConvexOn ℝ K f)
    (xstar : E) (hxstar : xstar ∈ K) (hxstar_min : ∀ x ∈ K, f xstar ≤ f x)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, 1 ≤ t → η t = min 1 (2 / (t : ℝ)))
    (x v : ℕ → E) (hrun : IsConditionalGradientRun K g η x v)
    (t : ℕ) (ht : 2 ≤ t) :
    f (x t) - f xstar ≤ 2 * β * D ^ 2 / t := by sorry

end OnlineConvexOpt.ProjectionFree

