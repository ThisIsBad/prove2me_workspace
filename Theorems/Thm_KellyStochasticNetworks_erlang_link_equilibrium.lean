import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang

namespace KellyStochasticNetworks

theorem erlang_link_equilibrium (lam mu : ℝ) (C : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (π : Fin (C + 1) → ℝ) (h : DetailedBalance π (erlangRates lam mu C)) (j : Fin (C + 1)) :
    π j = (lam / mu) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ) * π 0 := by sorry

end KellyStochasticNetworks
