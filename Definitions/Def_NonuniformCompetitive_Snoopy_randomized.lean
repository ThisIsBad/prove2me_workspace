import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_model

namespace NonuniformCompetitive.Snoopy

open MeasureTheory
open scoped ENNReal

/-- A randomized on-line snoopy-caching algorithm for block-transfer cost `p` (Karlin et al.
1994, §1, p. 542: "a probability distribution on a set of deterministic algorithms"): a
probability measure `μ` on an index type `ι` of coin-flip outcomes, and a deterministic on-line
algorithm for each outcome. All coins are flipped up front, which is the oblivious-adversary
setting. The field `meas` makes the cost on each fixed request sequence a measurable function of
the outcome, so that the lower integral below is the expected cost. -/
structure RandomizedAlgorithm (n p : ℕ) where
  ι : Type
  [ms : MeasurableSpace ι]
  μ : Measure ι
  prob : IsProbabilityMeasure μ
  alg : ι → OnlineAlgorithm n
  meas : ∀ σ : List (Req n), Measurable fun i => (alg i).cost p σ

/-- The expected cost `E C_A(σ)` of the randomized algorithm `A` on the request sequence `σ`. -/
noncomputable def RandomizedAlgorithm.expCost {n p : ℕ} (A : RandomizedAlgorithm n p)
    (σ : List (Req n)) : ℝ≥0∞ :=
  ∫⁻ i, (A.alg i).cost p σ ∂A.μ

/-- `A` is `c`-competitive against an oblivious adversary from the initial state `s₀`
(§1, p. 543): every deterministic algorithm in its support starts in `s₀`, and there is a
constant `a` such that on every admissible request sequence `σ`,
`E C_A(σ) ≤ c · C_opt(σ) + a`, where `C_opt(σ)` is the optimal off-line cost from `s₀`
(finite on admissible sequences) read as a real number. -/
def RandomizedAlgorithm.IsCompetitiveFrom {n p : ℕ} (A : RandomizedAlgorithm n p)
    (s₀ : State n) (c : ℝ) : Prop :=
  (∀ i, (A.alg i).after [] = s₀) ∧
  ∃ a : ℝ, ∀ σ : List (Req n), Admissible σ →
    A.expCost σ ≤ ENNReal.ofReal (c * (offlineCost p s₀ σ).toReal + a)

end NonuniformCompetitive.Snoopy
