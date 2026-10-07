import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_ArrivalProcess

open MeasureTheory ProbabilityTheory

namespace QueueingFundamentals.Foundations

/-- Eq. (1.15) and the Poisson CDF (pp.18–19): with independent `Exp(λ)` interarrival times, the
number of arrivals `N(t)` by time `t ≥ 0` satisfies
`P_n(t) = Pr{N(t) ≤ n} = ∫_t^∞ λ(λx)^n e^{-λx}/n! dx = ∑_{i=0}^n (λt)^i e^{-λt}/i!`,
and hence `Pr{N(t) = n} = (λt)^n e^{-λt}/n!`. -/
theorem poisson_count_cdf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    (hT : IsExpInterarrivals μ lam T) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | countingProcess T t ω ≤ n}).toReal =
        ∫ x in Set.Ioi t, lam * (lam * x) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * x)) ∧
      (μ {ω | countingProcess T t ω ≤ n}).toReal =
        ∑ i ∈ Finset.range (n + 1), (lam * t) ^ i * Real.exp (-(lam * t)) / (i.factorial : ℝ) ∧
      (μ {ω | countingProcess T t ω = n}).toReal =
        (lam * t) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * t)) := by sorry

end QueueingFundamentals.Foundations

