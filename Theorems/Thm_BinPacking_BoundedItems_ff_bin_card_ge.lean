import Mathlib
import Definitions.Def_BinPacking_BoundedItems_Model

namespace BinPacking.BoundedItems

/-- Johnson et al. 1974, Section 2, proof of Theorem 2.3, p. 308: if no element of `L`
exceeds `1/m` (`m ≥ 1` an integer), then every bin of the First-Fit packing of `L`, except
possibly the last bin, contains at least `m` elements. -/
theorem ff_bin_card_ge (m : ℕ) (hm : 1 ≤ m) (L : List ℝ) (hL : IsList L)
    (hLm : ∀ a ∈ L, a ≤ 1 / (m : ℝ)) :
    ∀ B ∈ (ffPack L).dropLast, m ≤ B.length := by sorry

end BinPacking.BoundedItems
