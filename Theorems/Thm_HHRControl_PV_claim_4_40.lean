import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Definitions.Def_HHRControl_PV_Construction428

namespace HHRControl.PV

open CookPvsNP

/-- Claim 4.40, p. 27: in an election of Construction 4.28 with `n(k + 1) + 1 ≤ m − k`, for every
partition of `V` into `V₁` and `V₂`, `c` is a plurality winner of `(C, V₁)` or of `(C, V₂)`. -/
theorem claim_4_40 (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ} (P : Fin N → Ranking (m + 2))
    (hP : IsConstruction428 m n k S P) (hmk : n * (k + 1) + 1 + k ≤ m) (V₁ : Finset (Fin N)) :
    candC m ∈ plurality.winners (m + 2) N P Finset.univ V₁ ∨
      candC m ∈ plurality.winners (m + 2) N P Finset.univ V₁ᶜ := by sorry

end HHRControl.PV

