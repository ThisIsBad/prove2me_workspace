import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization

namespace OnlineConvexOpt.Regularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma 5.4 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 75, PDF p. 97). With `g_0(x) = (1/η) R(x)` and `g_n(x) = ∇_n^⊤ x` for
`n ≥ 1` (`OnlineConvexOpt.Regularization.gFun`), a run of the RFTL algorithm (Algorithm 13)
satisfies, for every `u ∈ K`, `Σ_{n=0}^{T} g_n(u) ≥ Σ_{n=0}^{T} g_n(x_n)` — `x n` here is the
book's `x_{n+1}` under the chapter's 0-indexed shift, i.e. exactly the book's `Σ_{t=0}^T g_t(u)
≥ Σ_{t=0}^T g_t(x_{t+1})`. -/
theorem rftl_ftl_btl_comparison
    (K : Set E) (R : E → ℝ) (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ) (x grad : ℕ → E)
    (hRun : IsRFTLRun K R η f x grad) (T : ℕ) (u : E) (hu : u ∈ K) :
    ∑ n ∈ Finset.range (T + 1), gFun η R grad n u ≥
      ∑ n ∈ Finset.range (T + 1), gFun η R grad n (x n) := by sorry

end OnlineConvexOpt.Regularization
