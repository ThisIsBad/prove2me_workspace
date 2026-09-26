import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem family_size_traffic (lam mu nu : ℝ) (hlam : 0 < lam) (hmu : lam < mu) (hnu : 0 < nu)
    (α : ℕ → ℝ)
    (hα : ∀ j : ℕ, α (j + 1) = nu / (lam * ((j : ℝ) + 1)) * (lam / mu) ^ (j + 1)) :
    α 1 * (mu + lam) = nu + α 2 * (2 * mu)
      ∧ (∀ i : ℕ, α (i + 2) * (((i : ℝ) + 2) * lam + ((i : ℝ) + 2) * mu)
            = α (i + 1) * (((i : ℝ) + 1) * lam) + α (i + 3) * (((i : ℝ) + 3) * mu))
      ∧ HasSum (fun j : ℕ => α (j + 1)) (-(nu / lam) * Real.log (1 - lam / mu)) := by sorry

end KellyStochasticNetworks