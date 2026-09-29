import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.Regularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma 5.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 75, PDF p. 97). A run of the RFTL algorithm (Algorithm 13, with
regularizer `R`, gradient map `gradR`, step size `η`) on cost functions `f` over `K` satisfies,
for every horizon `T`, `RegretT ≤ Σ_{t=1}^T ∇_t^⊤(x_t - x_{t+1}) + (1/η) D_R²` — in the
chapter's 0-indexed convention (round `t ∈ ℕ` is the book's round `t + 1`), `Σ_{t ∈ range T}
⟪grad t, x t - x (t + 1)⟫ + (1/η) * D_R²`. `hRbdd` guards `RDiameterSq`'s defining supremum: the
book's `D_R` presupposes `R` bounded on `K` (true for its strongly-convex, smooth regularizers
over the bounded sets §5.1 works with), so without this hypothesis an unbounded `R x - R y`
would make `RDiameterSq` collapse to Mathlib's junk value `0` (`sSup` of an unbounded set),
trivializing the bound (FAITHFULNESS_TRAPS.md trap 5). -/
theorem rftl_regret_via_stability
    (K : Set E) (R : E → ℝ) (gradR : E → E) (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ)
    (x grad : ℕ → E) (hRun : IsRFTLRun K R η f x grad)
    (hRbdd : BddAbove (Set.image2 (fun p q => R p - R q) K K)) (T : ℕ) :
    RegretT K f x T ≤
      (∑ t ∈ Finset.range T, ⟪grad t, x t - x (t + 1)⟫_ℝ) + (1 / η) * RDiameterSq R K := by sorry

end OnlineConvexOpt.Regularization
