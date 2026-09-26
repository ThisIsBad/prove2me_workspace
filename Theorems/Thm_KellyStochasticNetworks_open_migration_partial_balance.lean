import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem open_migration_partial_balance {J : ℕ} (lam : Fin J → Fin J → ℝ)
    (mu nu α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (hlamdiag : ∀ j, lam j j = 0)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hα : ∀ j, 0 < α j) (hg : ∀ j, 0 < g j)
    (htraffic : OpenTraffic lam mu nu α) :
    (∀ (n : Fin J → ℕ) (j : Fin J), 1 ≤ n j →
        openMigrationPi α g φ n * ((∑ k, lam j k * φ j (n j)) + mu j * φ j (n j))
          = (∑ k, openMigrationPi α g φ (Tjk j k n) * (lam k j * φ k (n k + 1)))
            + openMigrationPi α g φ (Tout j n) * nu j)
      ∧ (∀ n : Fin J → ℕ,
        openMigrationPi α g φ n * (∑ k, nu k)
          = ∑ k, openMigrationPi α g φ (Tin k n) * (mu k * φ k (n k + 1))) := by sorry

end KellyStochasticNetworks