import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_ValueDist
import Definitions.Def_CHMSPricing_UnitDemand_SetSystem

namespace CHMSPricing.UnitDemand

/-- App. D.4, proof of Theorem 13, p. 20: the claim `cᵢ ≥ 4/9`. Two partition matroids on the
agents: agent `i` lies in part `P₁ = part₁⁻¹(part₁ i)` with capacity `k₁ = cap₁ (part₁ i) ≥ 1`
and in part `P₂ = part₂⁻¹(part₂ i)` with capacity `k₂ = cap₂ (part₂ i) ≥ 1`. If in every part
of either matroid the expected number of agents desiring service (`qᵢ = 1 − Fᵢ(pᵢ)`) is at most
a third of the part's capacity, then with probability at least `4/9` at most `k₁ − 1` agents of
`P₁` other than `i` and at most `k₂ − 1` agents of `P₂` other than `i` desire service — the
event `𝓔₁ ∩ 𝓔₂` under which `i` is always considered for service. -/
theorem considered_prob_ge_four_ninths {ι β₁ β₂ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq β₁] [DecidableEq β₂]
    (D : ι → ValueDist) (part₁ : ι → β₁) (cap₁ : β₁ → ℕ) (part₂ : ι → β₂) (cap₂ : β₂ → ℕ)
    (p : ι → ℝ)
    (hq₁ : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part₁ i' = b), (1 - (D i').cdf (p i'))
      ≤ (cap₁ b : ℝ) / 3)
    (hq₂ : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part₂ i' = b), (1 - (D i').cdf (p i'))
      ≤ (cap₂ b : ℝ) / 3)
    (i : ι) (hk₁ : 1 ≤ cap₁ (part₁ i)) (hk₂ : 1 ≤ cap₂ (part₂ i)) :
    (4 / 9 : ℝ) ≤ (prior D {v |
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)).card ≤ cap₁ (part₁ i) - 1 ∧
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)).card ≤ cap₂ (part₂ i) - 1}).toReal := by sorry

end CHMSPricing.UnitDemand

