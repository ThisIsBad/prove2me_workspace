import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem mm1_equilibrium (lam mu : ℝ) (hlam : 0 < lam) (hmu : lam < mu) :
    DetailedBalance (fun j : ℕ => (1 - lam / mu) * (lam / mu) ^ j) (mm1Rates lam mu)
      ∧ HasSum (fun j : ℕ => (1 - lam / mu) * (lam / mu) ^ j) 1 := by sorry

end KellyStochasticNetworks