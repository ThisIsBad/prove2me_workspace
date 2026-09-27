import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem ack_scheme_critical_rate_zero (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x)
    (hgrow : Filter.Tendsto (fun t : ℕ => ackAttemptRate h t / Real.log t)
        Filter.atTop Filter.atTop)
    (ν : ℝ) (hν : 0 < ν) :
    Summable (fun t : ℕ => ackSlotProb h ν (t + 1)) := by sorry

end KellyStochasticNetworks
