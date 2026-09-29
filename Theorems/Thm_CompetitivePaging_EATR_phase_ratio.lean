import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_EATR_eatr

open scoped ENNReal

namespace CompetitivePaging.EATR

theorem phase_ratio {M : Type*} [MetricSpace M] [DecidableEq M]
    (hunif : ∀ x y : M, x ≠ y → dist x y = 1) (a b : M) (hab : a ≠ b)
    (A : KServer.OnlineAlgorithm 2 M) (hA : IsLazy A) (σ : List M) (i i' : ℕ)
    (hph : IsCompletePhase a b σ i i') :
    eatrPhaseCost a b σ i i'
      ≤ (3 / 2 : ℝ) * (algPhaseCost A σ i i' + (mismatch a b A σ i : ℝ)
          - (mismatch a b A σ i' : ℝ)) := by sorry

end CompetitivePaging.EATR

