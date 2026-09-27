import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem ack_scheme_summable_h (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x) (hsum : Summable h)
    (ν : ℝ) (hν : 0 < ν) : ¬ Summable (fun t : ℕ => ackSlotProb h ν (t + 1)) := by sorry

end KellyStochasticNetworks
