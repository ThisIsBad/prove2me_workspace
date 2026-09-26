import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem open_migration_equilibrium {J : ℕ} (lam : Fin J → Fin J → ℝ)
    (mu nu α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (hlamdiag : ∀ j, lam j j = 0) (hlam : ∀ j k, 0 ≤ lam j k)
    (hmu : ∀ j, 0 ≤ mu j) (hnu : ∀ j, 0 ≤ nu j)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hα : ∀ j, 0 < α j) (htraffic : OpenTraffic lam mu nu α)
    (hg : ∀ j, HasSum (fun m : ℕ => α j ^ m / phiProd φ j m) (g j)) :
    FullBalance (openMigrationPi α g φ) (openMigrationRates lam mu nu φ)
      ∧ HasSum (openMigrationPi α g φ) 1 := by sorry

end KellyStochasticNetworks