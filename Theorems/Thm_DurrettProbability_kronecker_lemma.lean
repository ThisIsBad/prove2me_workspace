import Mathlib
import Definitions.Def_DurrettProbability_Series

open MeasureTheory ProbabilityTheory Filter

namespace DurrettProbability

theorem kronecker_lemma (a x : ℕ → ℝ) (hapos : ∀ n, 0 < a n) (hamono : Monotone a)
    (hatop : Tendsto a atTop atTop)
    (hconv : ∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, x n / a n) atTop (nhds L)) :
    Tendsto (fun n => (∑ m ∈ Finset.range n, x m) / a n) atTop (nhds 0) := by sorry

end DurrettProbability
