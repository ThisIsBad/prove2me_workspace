import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang

namespace KellyStochasticNetworks

theorem erlang_formula (lam mu : ℝ) (C : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (π : Fin (C + 1) → ℝ) (h : DetailedBalance π (erlangRates lam mu C))
    (hsum : ∑ j, π j = 1) :
    π (Fin.last C) = erlang (lam / mu) C := by sorry

end KellyStochasticNetworks
