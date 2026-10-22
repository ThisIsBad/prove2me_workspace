import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology

namespace RetailVariety.Statics

theorem theorem_2 (n i : ℕ) (hi : 1 ≤ i) (hin : i < n) (v : Fin n → ℝ) (hv : ∀ j, 0 < v j)
    (hanti : Antitone v) (c σ β : ℝ) (hc : 0 < c) (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    -- (a) sufficiently high selling price p, both demand models
    (∀ lam v0 : ℝ, 0 < lam → 0 < v0 →
      (∀ᶠ p in atTop,
          RetailVariety.Structure.profitI p c lam σ β v v0 (A n i) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1))) ∧
      (∀ᶠ p in atTop,
          RetailVariety.Structure.profitT p c lam v v0 (A n i) < RetailVariety.Structure.profitT p c lam v v0 (A n (i + 1)))) ∧
    -- (b) sufficiently low no-purchase preference v0, both demand models
    (∀ p lam : ℝ, c < p → 0 < lam →
      (∀ᶠ v0 in 𝓝[>] 0,
          RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1)) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n i)) ∧
      (c * ∑ j ∈ A n i, v j < p * v ⟨0, by omega⟩ →
        ∀ᶠ v0 in 𝓝[>] 0,
          RetailVariety.Structure.profitT p c lam v v0 (A n (i + 1)) < RetailVariety.Structure.profitT p c lam v v0 (A n i))) ∧
    -- (c) sufficiently high store volume lam, independent population model only
    (∀ p v0 : ℝ, c < p → 0 < v0 →
      ∀ᶠ lam in atTop,
          RetailVariety.Structure.profitI p c lam σ β v v0 (A n i) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1))) := by sorry

end RetailVariety.Statics

