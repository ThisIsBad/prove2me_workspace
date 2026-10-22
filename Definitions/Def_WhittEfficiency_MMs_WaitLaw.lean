import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

open MeasureTheory ProbabilityTheory

namespace WhittEfficiency.MMs

/-- The stationary FCFS waiting-time law in the M/M/s queue with individual service rate one.
An arrival seeing fewer than `s` customers waits zero; an arrival seeing `s + j` customers
waits for `j + 1` completions at total rate `s`. The arrival-state weights are the stationary
probabilities, using Poisson arrivals see time averages. -/
noncomputable def waitLaw (s : ℕ) (p : ℕ → ℝ) : Measure ℝ :=
  ENNReal.ofReal (∑ n ∈ Finset.range s, p n) • Measure.dirac 0 +
    Measure.sum (fun j : ℕ => ENNReal.ofReal (p (s + j)) •
      gammaMeasure ((j : ℝ) + 1) s)

end WhittEfficiency.MMs
