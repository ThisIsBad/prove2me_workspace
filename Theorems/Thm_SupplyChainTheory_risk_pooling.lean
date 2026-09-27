import Definitions.Def_SupplyChainTheory_flexibility

namespace SupplyChainTheory

theorem risk_pooling {N : ℕ} (h p : ℝ) (hh : 0 < h) (hp : 0 < p)
    (mu sig : Fin N → ℝ) (rho : Fin N → Fin N → ℝ)
    (hsig : ∀ i, 0 < sig i) (hrho : ∀ i j, rho i j ≤ 1) (hrho_diag : ∀ i, rho i i = 1)
    (hrho_symm : ∀ i j, rho i j = rho j i) :
    optNvCost h p
        (ProbabilityTheory.gaussianReal (∑ i, mu i) (Real.toNNReal (pooledVariance sig rho)))
      ≤ ∑ i, optNvCost h p
          (ProbabilityTheory.gaussianReal (mu i) (Real.toNNReal ((sig i) ^ 2))) := by sorry

end SupplyChainTheory

