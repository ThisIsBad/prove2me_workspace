import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_EATR_eatr

open scoped ENNReal

namespace CompetitivePaging.EATR

theorem phase_stale_uniform {M : Type*} [DecidableEq M] (a b : M) (hab : a ≠ b)
    (σ : List M) (i i' : ℕ) (hph : IsCompletePhase a b σ i i') :
    (stale (bookAfter a b (σ.take (i' - 1)))).card = numClean a b σ i i' + 1 ∧
      ∀ v ∈ stale (bookAfter a b (σ.take (i' - 1))),
        (lawAfter a b (σ.take (i' - 1))).toOuterMeasure {s | v ∈ servers s}
          = ((numClean a b σ i i' : ℝ≥0∞) + 1)⁻¹ := by sorry

end CompetitivePaging.EATR

