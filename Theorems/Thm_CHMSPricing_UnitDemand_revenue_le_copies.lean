import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism
import Definitions.Def_CHMSPricing_UnitDemand_MultiMechanism

namespace CHMSPricing.UnitDemand

/-- Lemma 3, p. 5 (existence form, pin P4): for every individually rational, truthful,
deterministic mechanism `𝒜` for an instance `ℐ` of the BMUMD there is a truthful mechanism
for the single-parameter instance with copies `ℐ^copies` (agents `J`, values `v_j ∼ F_j`
independent, the same set system `𝒥`) whose expected revenue is at least `ℛ^𝒜`. -/
theorem revenue_le_copies {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (A : MultiMechanism J m) (hA : IsTruthfulMulti D 𝒥 owner A) :
    ∃ A' : Mechanism J, IsTruthful D 𝒥 A' ∧ revenueMulti D A ≤ revenue D A' := by sorry

end CHMSPricing.UnitDemand

