import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Spm

namespace CHMSPricing.SpmMatroid

/-- §2.2 (p. 4): the expected revenue of an SPM is `ℛ^σ_p = ∑ᵢ cᵢ qᵢ pᵢ`, where
`cᵢ` is the probability that agent `i` is offered service at its turn and `qᵢ = 1 − Fᵢ(pᵢ)`. -/
theorem spmRevenue_eq_sum_offerProb {n : ℕ} (D : Fin n → ValueDist) (J : SetSystem (Fin n))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    spmRevenue D J σ p =
      ∑ i, (prior D {v | spmOffered J σ p v i}).toReal * (1 - (D i).cdf (p i)) * p i := by sorry

end CHMSPricing.SpmMatroid

