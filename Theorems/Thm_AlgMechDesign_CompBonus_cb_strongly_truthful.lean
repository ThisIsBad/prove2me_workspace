import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism

namespace AlgMechDesign.CompBonus

/-- Claim 5.2 (p. 188): for `n ≥ 2` agents and every optimal allocation algorithm (ties broken
arbitrarily), the Compensation-and-Bonus mechanism is strongly truthful: truth-telling with
minimal execution is dominant, and it is the only dominant strategy. -/
theorem cb_strongly_truthful {n k : ℕ} [NeZero n] (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hopt : IsOptimalAlloc alloc) :
    StronglyTruthful alloc (cbPay alloc) := by sorry

end AlgMechDesign.CompBonus

