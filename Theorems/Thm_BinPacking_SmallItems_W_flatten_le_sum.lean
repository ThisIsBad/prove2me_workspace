import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model
import Definitions.Def_BinPacking_SmallItems_Weight

namespace BinPacking.SmallItems

/-- Subadditivity of `W` (Section 4, p. 316): `W(X₁ ∪ ⋯ ∪ X_k) ≤ Σ W(X_i)`, for disjoint parts `X_i`
of a list of reals in `(0, 1]`, the union being the concatenation of the parts. -/
theorem W_flatten_le_sum (Xs : List (List ℝ)) (hL : IsList Xs.flatten) :
    W Xs.flatten ≤ (Xs.map W).sum := by sorry

end BinPacking.SmallItems
