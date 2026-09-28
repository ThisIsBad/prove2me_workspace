import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatGreedy_B1

namespace JohnsonApprox.MaxSatGreedy

theorem halt_left_dead (S : Finset Shared.Clause) (σ : State) (hσ : Reachable S σ) (hh : Halts σ) :
    ∀ C ∈ σ.LEFT, ∀ l ∈ C, l ∉ σ.TRUE ∧ l.neg ∈ σ.TRUE := by sorry

end JohnsonApprox.MaxSatGreedy

