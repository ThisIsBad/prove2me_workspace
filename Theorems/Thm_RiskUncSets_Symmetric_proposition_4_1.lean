import Definitions.Def_RiskUncSets_Symmetric_Setting

namespace RiskUncSets.Symmetric

theorem proposition_4_1 {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    (hq : q ∈ restrictedSimplex N) :
    (∀ (n : ℕ) (a : Fin N → Fin n → ℝ),
      CentrallySymmetric (permutohull q a) (sampleMean a)) ↔
    ∃ σ : Equiv.Perm (Fin N), q = fun i => 2 / (N : ℝ) - q (σ i) := by sorry

end RiskUncSets.Symmetric

