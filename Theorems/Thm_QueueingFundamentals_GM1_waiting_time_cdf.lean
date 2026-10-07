import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- Eq. (5.62): the FCFS line-delay and system-waiting-time CDFs seen by arrivals are
`W_q(t) = 1 - r_0 e^{-μ(1-r_0)t}` and `W(t) = 1 - e^{-μ(1-r_0)t}` for `t ≥ 0`. -/
theorem waiting_time_cdf (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1)
    (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0 : ℝ) 1) (hroot : beta A mu (r0 : ℂ) = (r0 : ℂ))
    (q : ℕ → ℝ) (hq : IsArrivalPointStationary A mu q) (t : ℝ) (ht : 0 ≤ t) :
    lineDelayCDF q mu t = 1 - r0 * Real.exp (-mu * (1 - r0) * t) ∧
      systemWaitCDF q mu t = 1 - Real.exp (-mu * (1 - r0) * t) := by sorry

end QueueingFundamentals.GM1

