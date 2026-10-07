import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

/-- Proof of Theorem 4(a), claim (B) and its consequence (pp. 22–23): in every feasible schedule
of the constructed instance with `Σ_j C_j ≤ y`, some job of `U` starts at a time `B_j ≤ σ`, and
`Σ_{j∉U} C_j ≤ u`. -/
theorem claim_B {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    (∃ j ∈ groupU a b, B j ≤ sigma a b) ∧
      ∑ j ∈ (groupU a b)ᶜ, completion (procTime a b) B j ≤ uCount a b := by sorry

end SchedComplexity.TotalCompletion

