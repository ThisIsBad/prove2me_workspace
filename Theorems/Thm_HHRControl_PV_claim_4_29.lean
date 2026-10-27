import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Definitions.Def_HHRControl_PV_Construction428

namespace HHRControl.PV

open CookPvsNP

/-- Claim 4.29, p. 24: in an election of Construction 4.28, if `B′` is a hitting set of `S` of size
`k`, then `w` is the unique plurality winner of the election `(B′ ∪ {c, w}, V)`. -/
theorem claim_4_29 (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ} (P : Fin N → Ranking (m + 2))
    (hP : IsConstruction428 m n k S P) (B' : Finset (Fin m)) (hcard : B'.card = k)
    (hhit : IsHittingSet S B') :
    plurality.winners (m + 2) N P (B'.image candB ∪ {candC m, candW m}) Finset.univ =
      {candW m} := by sorry

end HHRControl.PV

