import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Mechanism
import Definitions.Def_CHMSPricing_SpmMatroid_Spm

namespace CHMSPricing.SpmMatroid

/-- Theorem 5 (p. 6): under a matroid feasibility constraint and regular value distributions,
for every truthful mechanism `M`, the SPM `𝒮` with prices `pᵢ = Fᵢ⁻¹(1 − q^M_i)` that
approaches the agents in decreasing order of price earns at least half of `M`'s revenue. -/
theorem spm_two_approx_matroid {n : ℕ} (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (M : Mechanism (Fin n)) (hM : IsTruthful D J M)
    (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    revenue D M ≤ 2 * spmRevenue D J σ p := by sorry

end CHMSPricing.SpmMatroid

