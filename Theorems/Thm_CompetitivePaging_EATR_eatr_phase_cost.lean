import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_EATR_eatr

open scoped ENNReal

namespace CompetitivePaging.EATR

theorem eatr_phase_cost {M : Type*} [DecidableEq M] (a b : M) (hab : a ≠ b)
    (σ : List M) (i i' : ℕ) (hph : IsCompletePhase a b σ i i') :
    eatrPhaseCost a b σ i i'
      = (numClean a b σ i i' : ℝ) + (numClean a b σ i i' : ℝ) / ((numClean a b σ i i' : ℝ) + 1) := by sorry

end CompetitivePaging.EATR

