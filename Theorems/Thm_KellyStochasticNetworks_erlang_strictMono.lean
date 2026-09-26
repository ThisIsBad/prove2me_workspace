import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem erlang_strictMono (C : ℕ) :
    StrictMonoOn (fun ν : ℝ => erlang ν (C + 1)) (Set.Ioi 0)
      ∧ StrictMonoOn (fun ν : ℝ => ν * (1 - erlang ν (C + 1))) (Set.Ioi 0) := by sorry

end KellyStochasticNetworks