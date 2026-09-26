import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem loss_network_acceptance {J R : ℕ} (A : Fin J → Fin R → ℕ) (C : Fin J → ℕ)
    (ν : Fin R → ℝ) (hν : ∀ r, 0 < ν r) (r : Fin R) (hCr : ∀ j, A j r ≤ C j)
    (G GR : ℝ) (hG0 : G ≠ 0) (hGR0 : GR ≠ 0)
    (hG : HasSum (fun n : lossStates A C => lossWeight ν (n : Fin R → ℕ)) G⁻¹)
    (hGR : HasSum (fun n : lossStates A (fun j => C j - A j r) =>
              lossWeight ν (n : Fin R → ℕ)) GR⁻¹) :
    HasSum (fun n : lossStates A (fun j => C j - A j r) => G * lossWeight ν (n : Fin R → ℕ))
      (G / GR) := by sorry

end KellyStochasticNetworks