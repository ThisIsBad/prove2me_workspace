import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace UnrelatedSched.TwoApprox

open MatousekLP.Scheduling

/-- §2, proof of Theorem 1, p. 5: a schedule supported on a feasible point of (LP) that, on each
machine, has at most one job with `x̃_ij < 1` has loads at most `d_i + t`. -/
theorem rounding_load_bound {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (x : Matrix (Fin m) (Fin n) ℝ) (hx : LPFeasible P d t x)
    (σ : Fin n → Fin m) (hσ : SupportedOn x σ)
    (hfrac : ∀ i (j₁ j₂ : Fin n), σ j₁ = i → σ j₂ = i → x i j₁ < 1 → x i j₂ < 1 → j₁ = j₂) :
    ∀ i, load (realTimes P) σ i ≤ d i + t := by sorry

end UnrelatedSched.TwoApprox

