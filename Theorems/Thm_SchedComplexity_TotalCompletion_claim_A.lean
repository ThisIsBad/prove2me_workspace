import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

/-- Proof of Theorem 4(a), claim (A) (pp. 22–23): in every feasible schedule of the constructed
instance with `Σ_j C_j ≤ y`, every job outside `U` is processed before every job of `U`
(`{J_j | j ∉ U}` precedes `{J_j | j ∈ U}`), i.e. starts earlier. -/
theorem claim_A {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    ∀ j' j : Fin (numJobs a b), j' ∉ groupU a b → j ∈ groupU a b → B j' < B j := by sorry

end SchedComplexity.TotalCompletion

