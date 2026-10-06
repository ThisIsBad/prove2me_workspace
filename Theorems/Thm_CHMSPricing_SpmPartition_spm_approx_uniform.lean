import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem
import Definitions.Def_CHMSPricing_SpmPartition_Mechanism
import Definitions.Def_CHMSPricing_SpmPartition_Spm

namespace CHMSPricing.SpmPartition

theorem spm_approx_uniform {n : ℕ}
    (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (k : ℕ)
    (M : Mechanism (Fin n)) (hM : IsTruthful D (uniformSystem (Fin n) k) M)
    (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    revenue D M ≤ Real.exp 1 / (Real.exp 1 - 1) * spmRevenue D (uniformSystem (Fin n) k) σ p := by sorry

end CHMSPricing.SpmPartition

