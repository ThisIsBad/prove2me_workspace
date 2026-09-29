import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_ConditionalGradient
import Definitions.Def_OnlineConvexOpt_ProjectionFree_SmoothOn

namespace OnlineConvexOpt.ProjectionFree

/-- Theorem 7.1 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 127, PDF p. 149). The (offline) conditional gradient algorithm
(Algorithm 25) applied to `β`-smooth functions with step sizes `η_t = min{1, 2/t}` attains
`h_t ≤ 2βD²/t` for every `t ≥ 1`, where `h_t = f(x_t) - f(x⋆)` and `D` is the diameter of `K`.

`K` (convex, nonempty, diameter `≤ D`), `f` (convex and `β`-smooth on `K` with gradient map `g`,
§7.3's own setup, "minimizing a smooth convex function `f` over a convex set `K`", p. 126, PDF
148 — convexity used explicitly in the proof's Eq. (7.2) step, PDF 149), and `x⋆` (a global
minimizer of `f` over `K`) are the chapter's standing hypotheses for this theorem (p. 126-127),
stated here as explicit hypotheses. -/
theorem cg_convergence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (f : E → ℝ) (g : E → E) (β : ℝ) (hβpos : 0 < β) (hsmooth : SmoothOn K f g β)
    (hfconv : ConvexOn ℝ K f)
    (xstar : E) (hxstar : xstar ∈ K) (hxstar_min : ∀ x ∈ K, f xstar ≤ f x)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, 1 ≤ t → η t = min 1 (2 / (t : ℝ)))
    (x v : ℕ → E) (hrun : IsConditionalGradientRun K g η x v)
    (t : ℕ) (ht : 1 ≤ t) :
    f (x t) - f xstar ≤ 2 * β * D ^ 2 / t := by sorry

end OnlineConvexOpt.ProjectionFree
