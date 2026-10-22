import Mathlib

namespace StochIneqPO.Monotone

open MeasureTheory Filter Topology BoundedContinuousFunction

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Theorem 6 (i), p. 908: the family of distributions `Pᵢ = μ ∘ Xᵢ⁻¹`, `i ≥ 1`, is tight. -/
def LawsTight [TopologicalSpace E] (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  IsTightMeasureSet (Set.range fun i => μ.map (X i))

/-- Theorem 6 (ii), p. 908: the distributions `Pᵢ = μ ∘ Xᵢ⁻¹` converge weakly to a probability
measure `P`, i.e. `∫ f dPᵢ → ∫ f dP` for every bounded continuous `f : E → ℝ`. -/
def LawsConvergeWeakly [TopologicalSpace E] (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∃ P : ProbabilityMeasure E, ∀ f : E →ᵇ ℝ,
    Tendsto (fun i => ∫ x, f x ∂(μ.map (X i))) atTop (𝓝 (∫ x, f x ∂(P : Measure E)))

/-- Theorem 6 (iii), p. 908: `Xᵢ` converges in probability to a measurable random variable `Y`:
for every `ε > 0`, `μ {ω | d(Xᵢ ω, Y ω) ≥ ε} → 0`. -/
def ConvergesInProbability [PseudoMetricSpace E] (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∃ Y : Ω → E, Measurable Y ∧ TendstoInMeasure μ X atTop Y

/-- Theorem 6 (iv), p. 908: `Xᵢ` converges almost surely: for `μ`-almost every `ω` the sequence
`Xᵢ ω` converges in `E` (to `Y ω`). -/
def ConvergesAS [TopologicalSpace E] (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∃ Y : Ω → E, ∀ᵐ ω ∂μ, Tendsto (fun i => X i ω) atTop (𝓝 (Y ω))

end StochIneqPO.Monotone
