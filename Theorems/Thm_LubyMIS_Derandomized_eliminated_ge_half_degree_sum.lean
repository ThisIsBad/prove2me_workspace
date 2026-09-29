import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic

open MeasureTheory ProbabilityTheory

namespace LubyMIS.Derandomized

/-- First display of the proof of Theorem 1 (Luby 1986, §3.4, p. 1041), for an arbitrary random
selection `I′ = S ω` on a probability space `(Ω, μ)`:
`E[Y_k − Y_{k+1}] ≥ ½ ∑_i d(i) Pr[i ∈ I′ ∪ N(I′)] ≥ ½ ∑_i d(i) Pr[i ∈ N(I′)]`. -/
theorem eliminated_ge_half_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Ω → Finset V) (hS : ∀ i, MeasurableSet {ω | i ∈ S ω}) :
    (∫ ω, (eliminated H (S ω) : ℝ) ∂μ) ≥
        1 / 2 * ∑ i, (H.degree i : ℝ) * μ.real {ω | i ∈ S ω ∪ nbhd H (S ω)} ∧
      1 / 2 * ∑ i, (H.degree i : ℝ) * μ.real {ω | i ∈ S ω ∪ nbhd H (S ω)} ≥
        1 / 2 * ∑ i, (H.degree i : ℝ) * μ.real {ω | i ∈ nbhd H (S ω)} := by sorry

end LubyMIS.Derandomized
