import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.Regularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Theorem 5.2 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 74, PDF p. 96). The RFTL algorithm (Algorithm 13, regularizer `R` with
gradient map `gradR`, convex decision set `K`, step size `η`) attains, for every `u ∈ K`,
`Regret_T ≤ 2η Σ_{t=1}^T ‖∇_t‖*²_t + (R(u) - R(x_1))/η`. In the chapter's 0-indexed convention
(round `t ∈ ℕ` is the book's round `t + 1`), `‖∇_t‖*²_t` — the squared dual norm of `∇_t` local
to the segment `[x_t, x_{t+1}]` — is `nsq t`, any value satisfying `IsLocalDualNormSq R gradR
(x t) (x (t + 1)) (grad t) (nsq t)`, and `x_1` is `x 0`. -/
theorem rftl_regret_bound
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (R : E → ℝ) (hRconv : ConvexOn ℝ K R) (gradR : E → E)
    (hgradR : ∀ x ∈ K, HasGradientAt R (gradR x) x)
    (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ) (x grad : ℕ → E)
    (hRun : IsRFTLRun K R η f x grad)
    (nsq : ℕ → ℝ) (hnsq : ∀ t, IsLocalDualNormSq R gradR (x t) (x (t + 1)) (grad t) (nsq t))
    (T : ℕ) (u : E) (hu : u ∈ K) :
    RegretT K f x T ≤
      2 * η * (∑ t ∈ Finset.range T, nsq t) + (R u - R (x 0)) / η := by sorry

end OnlineConvexOpt.Regularization

