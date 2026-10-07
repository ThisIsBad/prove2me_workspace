import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol_v2
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization OnlineConvexOpt.FirstOrder



namespace OnlineConvexOpt.Regularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma 5.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 75, PDF p. 97). A run of the RFTL algorithm (Algorithm 13, with
regularizer `R`, step size `η > 0`) on convex cost functions `f` over the bounded convex
decision set `K` satisfies, for every horizon `T`,
`RegretT ≤ Σ_{t=1}^T ∇_t^⊤(x_t - x_{t+1}) + (1/η) D_R²` — in the chapter's 0-indexed
convention (round `t ∈ ℕ` is the book's round `t + 1`),
`Σ_{t ∈ range T} ⟪grad t, x t - x (t + 1)⟫ + (1/η) * D_R²`. `hRbdd` guards `RDiameterSq`'s
defining supremum (the book's `D_R` presupposes `R` bounded on `K`).

Corrected version: the retired statement dropped the OCO standing assumptions that the costs
`f_t` are convex on `K` (used in the proof's first step, Eq. (5.1)) and that `K` is a nonempty
bounded convex set (Algorithm 13's input, "a bounded, convex and closed set `K`"); `RegretT` is
now the `OnlineConvexOpt_FirstOrder_Protocol_v2` regret (genuine infimum over `K`), which under
these hypotheses is the book's `min` (the cumulative cost is bounded below on the bounded set
`K` by convexity at `x_t ∈ K` and the gradient there). -/
theorem rftl_regret_via_stability_v2
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty) (hKbdd : Bornology.IsBounded K)
    (R : E → ℝ) (gradR : E → E) (η : ℝ) (hη : 0 < η)
    (f : ℕ → E → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (x grad : ℕ → E) (hRun : IsRFTLRun K R η f x grad)
    (hRbdd : BddAbove (Set.image2 (fun p q => R p - R q) K K)) (T : ℕ) :
    RegretT K f x T ≤
      (∑ t ∈ Finset.range T, ⟪grad t, x t - x (t + 1)⟫_ℝ) + (1 / η) * RDiameterSq R K := by sorry

end OnlineConvexOpt.Regularization

