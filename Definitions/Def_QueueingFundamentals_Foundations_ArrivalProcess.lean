import Mathlib

open MeasureTheory ProbabilityTheory

namespace QueueingFundamentals.Foundations

/-- The interarrival times `T 0, T 1, T 2, …` (the book's `T`, "time between successive
arrivals", §1.7, p.18) are measurable, mutually independent, and each exponentially distributed
with rate `lam` (mean `1 / lam`) under the probability measure `μ`. -/
structure IsExpInterarrivals {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (lam : ℝ)
    (T : ℕ → Ω → ℝ) : Prop where
  measurable : ∀ i, Measurable (T i)
  indep : iIndepFun T μ
  law : ∀ i, μ.map (T i) = expMeasure lam

/-- The `n`-th arrival epoch `T 0 + ⋯ + T (n-1)` (the sum of the first `n` interarrival times;
`0` for `n = 0`). -/
def arrivalTime {Ω : Type*} (T : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, T i ω

/-- The arrival counting process `N(t)`: the number of arrivals in `[0, t]`, i.e. the number of
`n ≥ 1` whose `n`-th arrival epoch is at most `t` (so `N(0) = 0` when interarrival times are
positive). If infinitely many epochs are `≤ t`, `Set.ncard` returns `0`; for exponential
interarrival times this happens only on a null set. -/
noncomputable def countingProcess {Ω : Type*} (T : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t}.ncard

end QueueingFundamentals.Foundations
