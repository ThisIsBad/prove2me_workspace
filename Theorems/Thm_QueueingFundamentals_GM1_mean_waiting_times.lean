import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- Eq. (5.63): the mean line delay and mean system waiting time seen by arrivals,
`W_q = ∫_0^∞ [1 - W_q(t)] dt = r_0/(μ(1 - r_0))` and `W = ∫_0^∞ [1 - W(t)] dt = 1/(μ(1 - r_0))`. -/
theorem mean_waiting_times (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1)
    (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0 : ℝ) 1) (hroot : beta A mu (r0 : ℂ) = (r0 : ℂ))
    (q : ℕ → ℝ) (hq : IsArrivalPointStationary A mu q) :
    IntegrableOn (fun t => 1 - lineDelayCDF q mu t) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), (1 - lineDelayCDF q mu t) = r0 / (mu * (1 - r0)) ∧
      IntegrableOn (fun t => 1 - systemWaitCDF q mu t) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), (1 - systemWaitCDF q mu t) = 1 / (mu * (1 - r0)) := by sorry

end QueueingFundamentals.GM1

