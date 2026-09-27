import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem aloha_attempt_rate (f : ℝ) (hf : 0 < f) :
    (∀ t : ℕ, ackAttemptRate (alohaH f) (t + 1) = 1 + (t : ℝ) * f)
      ∧ Filter.Tendsto (fun t : ℕ => ackAttemptRate (alohaH f) t / Real.log t)
          Filter.atTop Filter.atTop := by sorry

end KellyStochasticNetworks
