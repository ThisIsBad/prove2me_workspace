import Definitions.Def_RiskUncSets_Symmetric_Setting

namespace RiskUncSets.Symmetric

theorem symRestrictedSimplex_subset_mixtures {N : ℕ} (hN : 0 < N)
    (q : Fin N → ℝ) (hq : q ∈ symRestrictedSimplex N) :
    ∃ lam : Fin (Nhat N) → ℝ,
      (∀ j, 0 ≤ lam j) ∧
      ∑ j, lam j = 1 ∧
      q = ∑ j, lam j • qbar j := by sorry

end RiskUncSets.Symmetric

