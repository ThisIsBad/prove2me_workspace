import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_MenuMech

namespace CHMSPricing.UnitDemand

/-- App. B, proof of Theorem 4, p. 14: the price-menu mechanism allocates a maximal feasible set
of services; viewed in `ℐ^copies`, its allocation is a maximal feasible set of desiring copies
(`S ∈ 𝒮_v`), for every arrival order, every prices and every value vector. -/
theorem menuMech_alloc_maxFeasDesiring {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (σ : Equiv.Perm (Fin m)) (p v : J → ℝ) :
    IsMaxFeasDesiring 𝒥 p v ((menuMech 𝒥 owner σ p).alloc v) := by sorry

end CHMSPricing.UnitDemand

