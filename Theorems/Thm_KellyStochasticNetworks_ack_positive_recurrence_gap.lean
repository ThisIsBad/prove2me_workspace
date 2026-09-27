import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem ack_positive_recurrence_gap :
    (∀ ν : ℝ, 0 < ν → ν ≤ Real.exp (-ν) → ν < 0.5672)
      ∧ (0.5672 : ℝ) < Real.log 2 := by sorry

end KellyStochasticNetworks
