import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
noncomputable section

namespace RiskUncSets.InnerApprox

/-- Proof of Theorem 4.5: `Π_q(𝒜) ⊆ 𝒰` iff there are `s_k, t_k ∈ ℝᴺ` with
`e′(s_k + t_k) ≥ v_k` and `s_{k,i} + t_{k,j} ≤ (u_k′ a_j) q_i`; for every `q ∈ ℝᴺ`. -/
theorem permutohull_subset_polytope_iff {N n m : ℕ} (q : Fin N → ℝ)
    (a : Fin N → Fin n → ℝ) (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) :
    permutohull q a ⊆ polytope u v ↔
      ∃ s t : Fin m → Fin N → ℝ, (∀ k, v k ≤ ∑ i, (s k i + t k i)) ∧
        ∀ k i j, s k i + t k j ≤ (u k ⬝ᵥ a j) * q i := by sorry

end RiskUncSets.InnerApprox

