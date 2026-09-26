import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem loss_network_uncapacitated {R : ℕ} (ν : Fin R → ℝ) (hν : ∀ r, 0 < ν r) :
    FullBalance
        (fun n : Fin R → ℕ => ∏ r, Real.exp (-ν r) * (ν r ^ n r / (Nat.factorial (n r) : ℝ)))
        (openMigrationRates (fun _ _ => (0 : ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ)))
      ∧ HasSum
        (fun n : Fin R → ℕ => ∏ r, Real.exp (-ν r) * (ν r ^ n r / (Nat.factorial (n r) : ℝ))) 1
      ∧ DetailedBalance
        (fun n : Fin R → ℕ => ∏ r, Real.exp (-ν r) * (ν r ^ n r / (Nat.factorial (n r) : ℝ)))
        (openMigrationRates (fun _ _ => (0 : ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ))) := by sorry

end KellyStochasticNetworks