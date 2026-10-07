import Mathlib
import Definitions.Def_SchedComplexity_NoWait_DirectedGraphs
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

/-- Theorem 5(a), the equivalence (p. 25): for an admissible `ι`, `λ ≥ 1` and `μ ≥ 2λ + 3`, the
directed graph `adj` on `n` vertices has a Hamilton path iff the constructed
`n|m|F,no wait|C_max` instance (`m = n(n−1)+2`) has a feasible schedule with
`C_max ≤ (n − 1)(μ + 2λ) + mμ`. -/
theorem theorem_5a_equiv {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) :
    HasHamiltonPath adj ↔
      ∃ B, IsNoWaitSchedule (procTimes adj ι lam mu) B ∧
        ∀ ℓ, completion (procTimes adj ι lam mu) B ℓ ≤
          (n - 1) * (mu + 2 * lam) + numMachines n * mu := by sorry

end SchedComplexity.NoWait

