import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem
import Definitions.Def_CHMSPricing_SpmPartition_Mechanism
import Definitions.Def_CHMSPricing_SpmPartition_Spm

namespace CHMSPricing.SpmPartition

theorem spm_e_div_e_sub_one_approx_partition {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (part : Fin n → β) (cap : β → ℕ)
    (M : Mechanism (Fin n)) (hM : IsTruthful D (partitionSystem part cap) M)
    (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    revenue D M ≤
      Real.exp 1 / (Real.exp 1 - 1) * spmRevenue D (partitionSystem part cap) σ p := by sorry

end CHMSPricing.SpmPartition

