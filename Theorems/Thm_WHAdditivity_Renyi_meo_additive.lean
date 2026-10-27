import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem meo_additive (N : ℕ) (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (p : ℝ) (hp1 : 1 ≤ p)
    (hp2 : p ≤ 2) :
    BddBelow (outputEntropies p (tensorChannel d fun j => wernerHolevo (d j))) ∧
    (∀ j, BddBelow (outputEntropies p (wernerHolevo (d j)))) ∧
    minOutputEntropy p (tensorChannel d fun j => wernerHolevo (d j)) =
      ∑ j, minOutputEntropy p (wernerHolevo (d j)) := by sorry

end WHAdditivity.Renyi

