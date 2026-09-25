import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang

namespace KellyStochasticNetworks

theorem erlang_deriv (ν : ℝ) (C : ℕ) (hν : 0 < ν) :
    HasDerivAt (fun v : ℝ => erlang v (C + 1))
      (-(1 - erlang ν (C + 1)) * (erlang ν (C + 1) - erlang ν C)) ν := by sorry

end KellyStochasticNetworks
