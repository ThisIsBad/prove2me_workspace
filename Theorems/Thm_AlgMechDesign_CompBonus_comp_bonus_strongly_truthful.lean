import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism

namespace AlgMechDesign.CompBonus

/-- Theorem 5.1 (p. 188): for `n ≥ 2` agents and every optimal allocation algorithm (ties broken
arbitrarily), the Compensation-and-Bonus mechanism is a strongly truthful implementation of the
task scheduling problem: it is strongly truthful, and whenever every agent plays a dominant
strategy for its true type the output attains the optimal make-span. -/
theorem comp_bonus_strongly_truthful {n k : ℕ} [NeZero n] (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hopt : IsOptimalAlloc alloc) :
    StronglyTruthful alloc (cbPay alloc) ∧ ImplementsOptimum alloc (cbPay alloc) := by sorry

end AlgMechDesign.CompBonus

