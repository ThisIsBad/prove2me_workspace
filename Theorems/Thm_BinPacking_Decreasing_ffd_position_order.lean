import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

namespace BinPacking.Decreasing

/-- Claim 3.4.6 (p. 313), restated through Claim 3.4.5 (the positions of `S_h` are those that
the items after the first `h` fill in the FFD packing `PF`). Let `S = sortDesc L` with
`L ⊆ [1/6, 1]` and `h` the number of elements of `S` exceeding `1/3`. If items `i` and `i'`
of `S`, both after the first `h`, fill positions `(j, k)` and `(j', k')` of `PF`, the item
`i` is not the last one of its bin (`k < k_j`), and `(j, k) ≤ (j', k')` lexicographically,
then `i ≤ i'`. -/
theorem ffd_position_order (L : List ℝ) (hL : IsList L)
    (h6 : ∀ a ∈ L, (1 / 6 : ℝ) ≤ a) (i i' : Fin (sortDesc L).length)
    (hi : ((sortDesc L).filter (fun a => decide ((1 / 3 : ℝ) < a))).length ≤ (i : ℕ))
    (hi' : ((sortDesc L).filter (fun a => decide ((1 / 3 : ℝ) < a))).length ≤ (i' : ℕ))
    (hk : slotOf ffChoice (sortDesc L) i + 1 <
      ((run ffChoice (sortDesc L)).getD (binOf ffChoice (sortDesc L) i) []).length)
    (hle : binOf ffChoice (sortDesc L) i < binOf ffChoice (sortDesc L) i' ∨
      (binOf ffChoice (sortDesc L) i = binOf ffChoice (sortDesc L) i' ∧
        slotOf ffChoice (sortDesc L) i ≤ slotOf ffChoice (sortDesc L) i')) :
    i ≤ i' := by sorry

end BinPacking.Decreasing

