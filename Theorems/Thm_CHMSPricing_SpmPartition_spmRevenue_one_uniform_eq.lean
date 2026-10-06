import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem
import Definitions.Def_CHMSPricing_SpmPartition_Spm

namespace CHMSPricing.SpmPartition

theorem spmRevenue_one_uniform_eq {n : ℕ} (D : Fin n → ValueDist)
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    spmRevenue D (uniformSystem (Fin n) 1) σ p =
      ∑ k : Fin n, oneUnitOfferProb (fun j => 1 - (D (σ j)).cdf (p (σ j))) k *
        p (σ k) * (1 - (D (σ k)).cdf (p (σ k))) := by sorry

end CHMSPricing.SpmPartition

