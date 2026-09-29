import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_EATR_eatr

open scoped ENNReal

namespace CompetitivePaging.EATR

theorem eatr_competitive {n : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]
    (e : Fin n ≃ M) (hn : 2 ≤ n) (hunif : ∀ x y : M, x ≠ y → dist x y = 1) :
    ∃ c : ℝ, ∀ σ : List M,
      eatrExpCost (e ⟨0, by omega⟩) (e ⟨1, hn⟩) σ
        ≤ (3 / 2 : ℝ) * KServer.offlineCost ![e ⟨0, by omega⟩, e ⟨1, hn⟩] σ + c := by sorry

end CompetitivePaging.EATR

