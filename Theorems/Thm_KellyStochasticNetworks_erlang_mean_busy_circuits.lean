import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang

namespace KellyStochasticNetworks

theorem erlang_mean_busy_circuits (lam mu : ℝ) (C : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (π : Fin (C + 1) → ℝ) (h : DetailedBalance π (erlangRates lam mu C))
    (hsum : ∑ j, π j = 1) :
    ∑ j : Fin (C + 1), ((j : ℕ) : ℝ) * π j
      = (lam / mu) * (1 - erlang (lam / mu) C) := by sorry

end KellyStochasticNetworks
