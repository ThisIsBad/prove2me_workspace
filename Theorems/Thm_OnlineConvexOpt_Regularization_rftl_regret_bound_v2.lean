import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol_v2
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization OnlineConvexOpt.FirstOrder



namespace OnlineConvexOpt.Regularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Theorem 5.2 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 74, PDF p. 96). The RFTL algorithm (Algorithm 13, regularizer `R` with
gradient map `gradR`, convex decision set `K`, step size `η > 0`) run on convex cost functions
`f` attains, for every comparator `u ∈ K`,
`Σ_{t=1}^T (f_t(x_t) - f_t(u)) ≤ 2η Σ_{t=1}^T ‖∇_t‖*²_t + (R(u) - R(x_1))/η`
— the book's "`Regret_T ≤ …` for every `u ∈ K`", i.e. the regret against the fixed comparator
`u`, which is exactly what its proof (Lemma 5.4, "for every `u ∈ K`") establishes. In the
chapter's 0-indexed convention (round `t ∈ ℕ` is the book's round `t + 1`), `‖∇_t‖*²_t` — the
squared dual norm of `∇_t` local to the segment `[x_t, x_{t+1}]` — is `nsq t`, any value
satisfying `IsLocalDualNormSq R gradR (x t) (x (t + 1)) (grad t) (nsq t)`, and `x_1` is `x 0`.

Corrected version: the retired statement dropped the OCO standing assumption that the costs
`f_t` are convex on `K` (the proof's first step, Eq. (5.1), is the convexity inequality
`f_t(x_t) - f_t(u) ≤ ∇_t^⊤(x_t - u)`), and it bounded the global regret `RegretT` (the supremum
over all comparators) by a right-hand side depending on the particular `u`, which is false at
`u = x_1`; the conclusion is now the per-comparator inequality the book proves. -/
theorem rftl_regret_bound_v2
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (R : E → ℝ) (hRconv : ConvexOn ℝ K R) (gradR : E → E)
    (hgradR : ∀ x ∈ K, HasGradientAt R (gradR x) x)
    (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (x grad : ℕ → E) (hRun : IsRFTLRun K R η f x grad)
    (nsq : ℕ → ℝ) (hnsq : ∀ t, IsLocalDualNormSq R gradR (x t) (x (t + 1)) (grad t) (nsq t))
    (T : ℕ) (u : E) (hu : u ∈ K) :
    (∑ t ∈ Finset.range T, (f t (x t) - f t u)) ≤
      2 * η * (∑ t ∈ Finset.range T, nsq t) + (R u - R (x 0)) / η := by sorry

end OnlineConvexOpt.Regularization

