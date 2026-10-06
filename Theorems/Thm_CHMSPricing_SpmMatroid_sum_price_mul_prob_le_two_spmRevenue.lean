import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Spm

namespace CHMSPricing.SpmMatroid

/-- §4.1, end of the proof of Theorem 5 (p. 7): under a matroid constraint, if the prices
`pᵢ ∈ [loᵢ, hiᵢ]` have acceptance probabilities `qᵢ = 1 − Fᵢ(pᵢ)` with `∑_{i ∈ T} qᵢ ≤ rank(T)`
for every `T`, and the agents are approached in decreasing order of price, then
`∑ᵢ pᵢ qᵢ ≤ 2 ℛ^σ_p`. -/
theorem sum_price_mul_prob_le_two_spmRevenue {n : ℕ} (D : Fin n → ValueDist)
    (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi)
    (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, (1 - (D i).cdf (p i)) ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    ∑ i, p i * (1 - (D i).cdf (p i)) ≤ 2 * spmRevenue D J σ p := by sorry

end CHMSPricing.SpmMatroid

