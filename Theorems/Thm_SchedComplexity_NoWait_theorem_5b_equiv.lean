import Mathlib
import Definitions.Def_SchedComplexity_NoWait_DirectedGraphs
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

/-- Theorem 5(b), the equivalence (p. 25): for the instance constructed as in (a), with an
admissible `ι`, `λ ≥ 1` and `μ ≥ 2λ + 3`, the graph has a Hamilton path iff some feasible
no-wait schedule has `Σ_j C_j ≤ ½ n(n − 1)(μ + 2λ) + nmμ` (compared in `ℚ`, as printed). -/
theorem theorem_5b_equiv {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) :
    HasHamiltonPath adj ↔
      ∃ B, IsNoWaitSchedule (procTimes adj ι lam mu) B ∧
        ((∑ ℓ, completion (procTimes adj ι lam mu) B ℓ : ℕ) : ℚ) ≤
          (1 / 2 : ℚ) * n * ((n : ℚ) - 1) * ((mu : ℚ) + 2 * lam) +
            (n : ℚ) * (numMachines n : ℚ) * mu := by sorry

end SchedComplexity.NoWait

