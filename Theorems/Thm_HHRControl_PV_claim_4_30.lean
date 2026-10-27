import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Definitions.Def_HHRControl_PV_Construction428

namespace HHRControl.PV

open CookPvsNP

/-- Claim 4.30, p. 24: in an election of Construction 4.28, let `D ⊆ B ∪ {w}`. If `c` is not the
unique plurality winner of `(D ∪ {c}, V)`, then `D = B′ ∪ {w}` for a set `B′ ⊆ B` such that `w` is
the unique plurality winner of `(B′ ∪ {c, w}, V)` and `B′` is a hitting set of `S` of size at most
`k`. -/
theorem claim_4_30 (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ} (P : Fin N → Ranking (m + 2))
    (hP : IsConstruction428 m n k S P) (D : Finset (Fin (m + 2)))
    (hD : D ⊆ Finset.univ.image candB ∪ {candW m})
    (hc : plurality.winners (m + 2) N P (insert (candC m) D) Finset.univ ≠ {candC m}) :
    ∃ B' : Finset (Fin m), D = B'.image candB ∪ {candW m} ∧
      plurality.winners (m + 2) N P (B'.image candB ∪ {candC m, candW m}) Finset.univ =
        {candW m} ∧
      B'.card ≤ k ∧ IsHittingSet S B' := by sorry

end HHRControl.PV

