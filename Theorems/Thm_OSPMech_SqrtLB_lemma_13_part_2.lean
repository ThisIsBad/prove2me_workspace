import Mathlib
import Definitions.Def_OSPMech_SqrtLB_Model

namespace OSPMech.SqrtLB
theorem lemma_13_part_2 (c : ℕ) (hc : 2 ≤ c) (L Mid H : ℝ) (hL : 0 < L)
    (hM : ((c ^ 2 : ℕ) : ℝ) * L ≤ Mid) (hH : ((c ^ 2 : ℕ) : ℝ) * c * Mid ≤ H)
    (t : ImplTree (c ^ 2) (Fin (c ^ 2) → ℕ)) (p : (Fin (c ^ 2) → ℝ) → Fin (c ^ 2) → ℝ)
    (hsched : IsSchedule (c ^ 2) (fun _ => {L, Mid, H}) t)
    (hosp : IsOSP (fun _ => {L, Mid, H}) schedCost t p)
    (k : ℝ) (hk : k < c) (happrox : IsKApprox (c ^ 2) k (fun _ => {L, Mid, H}) t)
    (r : ℕ) (i : Fin (c ^ 2)) (pos : List ℕ) (hr : r + 1 ≤ c ^ 2 - c)
    (hdiv : IsKthDiverger (fun _ => {L, Mid, H}) t H r i pos) :
    ∀ x : Fin (c ^ 2) → ℝ, InDomain (fun _ => {L, Mid, H}) x → Compatible t pos x → x i = H →
      outcome t x i = 0 := by sorry
end OSPMech.SqrtLB

