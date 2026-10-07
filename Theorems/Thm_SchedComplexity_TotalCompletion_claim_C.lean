import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

/-- Proof of Theorem 4(a), claim (C) (pp. 22–23): in every feasible schedule of the constructed
instance with `Σ_j C_j ≤ y`, exactly `t` jobs start before the last job `J_n`. -/
theorem claim_C {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    (Finset.univ.filter fun j => B j < B (lastJob a b)).card = t := by sorry

end SchedComplexity.TotalCompletion

