import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Spm

namespace CHMSPricing.SpmMatroid

/-- §4.1, proof of Theorem 5 (p. 7, first display): in one run of the SPM under a matroid
constraint, with nonnegative prices offered in decreasing order and weights `qᵢ ≥ 0` satisfying
`∑_{i ∈ T} qᵢ ≤ rank(T)` for every `T`, the revenue lost on the blocked agents,
`∑_{i blocked} pᵢ qᵢ`, is at most the revenue `∑_{i ∈ S} pᵢ` of the served set `S`. -/
theorem blocked_loss_le_served_revenue {n : ℕ} (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, q i ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) (v : Fin n → ℝ) :
    ∑ i ∈ spmBlocked J σ p v, p i * q i ≤
      ∑ i ∈ spmServed J σ p v, p i := by sorry

end CHMSPricing.SpmMatroid

