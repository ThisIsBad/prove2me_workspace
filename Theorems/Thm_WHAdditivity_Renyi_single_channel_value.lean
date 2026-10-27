import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem single_channel_value (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1 ≤ p) :
    (∀ φ : Fin d → ℂ, IsUnitVector φ →
      wernerHolevo d (pureState φ) = ((d : ℂ) - 1)⁻¹ • (1 - pureState (star φ))) ∧
    (∀ φ : Fin d → ℂ, IsUnitVector φ →
      renyiEntropy p (wernerHolevo d (pureState φ)) = Real.log ((d : ℝ) - 1)) ∧
    BddBelow (outputEntropies p (wernerHolevo d)) ∧
    minOutputEntropy p (wernerHolevo d) = Real.log ((d : ℝ) - 1) := by sorry

end WHAdditivity.Renyi

