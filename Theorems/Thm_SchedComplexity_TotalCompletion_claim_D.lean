import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

/-- Proof of Theorem 4(a), claim (D) (pp. 22–23): in every feasible schedule (integral starting
times) of the constructed instance with `Σ_j C_j ≤ y`, the last job starts exactly at its
release date: `B_n = tτ + b`. -/
theorem claim_D {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    B (lastJob a b) = t * tau a b + b := by sorry

end SchedComplexity.TotalCompletion

