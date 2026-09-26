import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

theorem tree_reversible {E : Type*} [Fintype E] (q : E → E → ℝ) (π : E → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (htw : TwoWay q) (hdiag : ∀ x, q x x = 0)
    (hπ : ∀ x, 0 < π x) (hinv : IsInvariant q π) (htree : (commGraph q).IsTree) :
    DetailedBalance q π := by sorry

end SerfozoStochasticNetworks
