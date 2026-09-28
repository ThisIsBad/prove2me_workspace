import Mathlib
import Definitions.Def_KServer_model

namespace KServer

open MeasureTheory

/-- A **randomized online `k`-server algorithm** on the metric space `M`, as a
mixed strategy: a probability measure `μ` on an index type `ι` of coin-flip
outcomes together with, for each outcome, a deterministic online algorithm.
The whole random choice is made up front (equivalently, all coins are flipped
before the first request), which is the standard mixed-strategy presentation
of randomized online algorithms against oblivious adversaries. The field
`meas` requires the cost of the drawn algorithm on each fixed request
sequence to be a measurable function of the outcome. -/
structure RandomizedAlgorithm (k : ℕ) (M : Type*) [MetricSpace M] where
  ι : Type
  [ms : MeasurableSpace ι]
  μ : Measure ι
  prob : IsProbabilityMeasure μ
  alg : ι → OnlineAlgorithm k M
  meas : ∀ σ : List M, Measurable fun i => (alg i).cost σ

/-- The **expected cost** of the randomized algorithm `A` on the request
sequence `σ`: the lower Lebesgue integral, over the coin-flip outcomes, of the
(nonnegative) cost of the drawn deterministic algorithm. -/
noncomputable def RandomizedAlgorithm.expCost {k : ℕ} {M : Type*} [MetricSpace M]
    (A : RandomizedAlgorithm k M) (σ : List M) : ENNReal :=
  ∫⁻ i, ENNReal.ofReal ((A.alg i).cost σ) ∂A.μ

/-- The randomized algorithm `A` is **`c`-competitive from `C₀`** (against
oblivious adversaries): every deterministic algorithm in its support starts in
the configuration `C₀`, and there is a constant `a` (independent of the
request sequence) such that on every request sequence the expected cost of `A`
is at most `c` times the optimal offline cost from `C₀`, plus `a`. -/
def RandomizedAlgorithm.IsCompetitiveFrom {k : ℕ} {M : Type*} [MetricSpace M]
    (A : RandomizedAlgorithm k M) (C₀ : Config k M) (c : ℝ) : Prop :=
  (∀ i, (A.alg i).conf [] = C₀) ∧
  ∃ a : ℝ, ∀ σ : List M,
    A.expCost σ ≤ ENNReal.ofReal (c * offlineCost C₀ σ + a)

end KServer
