import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatGreedy_B1

namespace JohnsonApprox.MaxSatGreedy

theorem greedy_maxsat_ratio (k : ℕ) (hk : 1 ≤ k) :
    (∀ (S : Finset Shared.Clause), Shared.InMS k S → ∀ X : Finset Shared.Clause, Choosable S X →
        k * Shared.opt S ≤ (k + 1) * X.card) ∧
      (∃ (S : Finset Shared.Clause), Shared.InMS k S ∧ ∃ X : Finset Shared.Clause, Choosable S X ∧
        0 < X.card ∧ k * Shared.opt S = (k + 1) * X.card) := by sorry

end JohnsonApprox.MaxSatGreedy

