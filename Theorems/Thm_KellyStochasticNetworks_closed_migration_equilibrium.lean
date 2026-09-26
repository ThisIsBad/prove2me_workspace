import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem closed_migration_equilibrium {J : ℕ} (lam : Fin J → Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (α : Fin J → ℝ) (G : ℝ) (hG : G ≠ 0)
    (hlamdiag : ∀ j, lam j j = 0) (hlam : ∀ j k, 0 ≤ lam j k)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (htraffic : ClosedTraffic lam α) :
    FullBalance (fun n : Fin J → ℕ => G⁻¹ * ∏ j, (α j ^ n j / phiProd φ j (n j)))
      (closedMigrationRates lam φ) := by sorry

end KellyStochasticNetworks