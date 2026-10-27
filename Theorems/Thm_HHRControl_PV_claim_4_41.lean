import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Definitions.Def_HHRControl_PV_Construction428

namespace HHRControl.PV

open CookPvsNP

/-- Claim 4.41, p. 28: in an election of Construction 4.28 with `n(k + 1) + 1 ≤ m − k`, the
following are equivalent: (1) `S` has a hitting set of size at most `k`; (2) `V` can be partitioned
so that `w` is the unique plurality winner in model TP; (3) `V` can be partitioned so that `c` is
not the unique plurality winner in model TP. -/
theorem claim_4_41 (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ} (P : Fin N → Ranking (m + 2))
    (hP : IsConstruction428 m n k S P) (hmk : n * (k + 1) + 1 + k ≤ m) :
    ((∃ B' : Finset (Fin m), B'.card ≤ k ∧ IsHittingSet S B') ↔
        ∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ = {candW m}) ∧
      ((∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ = {candW m}) ↔
        ∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ ≠ {candC m}) := by sorry

end HHRControl.PV

