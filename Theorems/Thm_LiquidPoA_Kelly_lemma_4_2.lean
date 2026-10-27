import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- Lemma 4.2, p. 13: the liquid price of anarchy is bounded by the supremum (6), with equality under the equilibrium condition. -/
theorem lemma_4_2 {n : ℕ} (hn : 2 ≤ n) (M : Mechanism n)
    (hM : IsRAMechanism M) :
    (lpoa M ≤ ⨆ (s : Fin n → ℝ) (_ : InX s),
      ratio M s (⟨0, by omega⟩ : Fin n)) ∧
    ((∀ s, InX s →
      IsEquilibrium M (worstGame M s (⟨0, by omega⟩ : Fin n)) s) →
      lpoa M = ⨆ (s : Fin n → ℝ) (_ : InX s),
        ratio M s (⟨0, by omega⟩ : Fin n)) := by sorry

end LiquidPoA.Kelly

