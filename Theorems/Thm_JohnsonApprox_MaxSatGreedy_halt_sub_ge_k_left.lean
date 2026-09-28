import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatGreedy_B1

namespace JohnsonApprox.MaxSatGreedy

theorem halt_sub_ge_k_left (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) (σ : State)
    (hσ : Reachable S σ) (hh : Halts σ) :
    k * σ.LEFT.card ≤ σ.SUB.card ∧ Disjoint σ.SUB σ.LEFT ∧ σ.SUB ∪ σ.LEFT = S := by sorry

end JohnsonApprox.MaxSatGreedy

