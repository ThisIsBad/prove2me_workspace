import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem open_migration_reversed {J : ℕ} (lam : Fin J → Fin J → ℝ)
    (mu nu α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (hlamdiag : ∀ j, lam j j = 0)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hα : ∀ j, 0 < α j) (hg : ∀ j, 0 < g j) :
    (∀ (n : Fin J → ℕ) (j k : Fin J), j ≠ k → 1 ≤ n j →
        reversedRates (openMigrationPi α g φ) (openMigrationRates lam mu nu φ) n (Tjk j k n)
          = (α k * lam k j / α j) * φ j (n j))
      ∧ (∀ (n : Fin J → ℕ) (j : Fin J), 1 ≤ n j →
        reversedRates (openMigrationPi α g φ) (openMigrationRates lam mu nu φ) n (Tout j n)
          = (nu j / α j) * φ j (n j))
      ∧ (∀ (n : Fin J → ℕ) (k : Fin J),
        reversedRates (openMigrationPi α g φ) (openMigrationRates lam mu nu φ) n (Tin k n)
          = α k * mu k) := by sorry

end KellyStochasticNetworks