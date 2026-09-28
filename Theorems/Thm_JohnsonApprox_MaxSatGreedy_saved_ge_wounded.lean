import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatGreedy_B1

namespace JohnsonApprox.MaxSatGreedy

theorem saved_ge_wounded (σ σ' : State) (y : Shared.Literal) (h : StepWith σ y σ') :
    (σ'.LEFT.filter (fun C => y.neg ∈ C)).card ≤ (σ.YT y).card := by sorry

end JohnsonApprox.MaxSatGreedy

