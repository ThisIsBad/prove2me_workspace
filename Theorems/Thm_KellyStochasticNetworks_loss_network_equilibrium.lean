import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem loss_network_equilibrium {J R : ℕ} (A : Fin J → Fin R → ℕ) (C : Fin J → ℕ)
    (ν : Fin R → ℝ) (hν : ∀ r, 0 < ν r) (G : ℝ) (hG0 : G ≠ 0)
    (hG : HasSum (fun n : lossStates A C => lossWeight ν (n : Fin R → ℕ)) G⁻¹) :
    DetailedBalance (fun n : lossStates A C => G * lossWeight ν (n : Fin R → ℕ))
        (truncatedRates
          (openMigrationRates (fun _ _ => (0 : ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ)))
          (lossStates A C))
      ∧ HasSum (fun n : lossStates A C => G * lossWeight ν (n : Fin R → ℕ)) 1 := by sorry

end KellyStochasticNetworks