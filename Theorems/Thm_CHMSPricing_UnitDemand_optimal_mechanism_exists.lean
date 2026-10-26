import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism

namespace CHMSPricing.UnitDemand

/-- Theorem 19, p. 12 (existence form, pin P4): with regular distributions there is a truthful
mechanism (Myerson's) whose expected revenue `ℛ^ℳ` is at least `ℛ^𝒜` for every truthful
mechanism `𝒜`. -/
theorem optimal_mechanism_exists {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular) (𝒥 : SetSystem ι) :
    ∃ Mstar : Mechanism ι, IsTruthful D 𝒥 Mstar ∧
      ∀ A : Mechanism ι, IsTruthful D 𝒥 A → revenue D A ≤ revenue D Mstar := by sorry

end CHMSPricing.UnitDemand

