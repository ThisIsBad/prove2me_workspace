import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- Lemma 1: for classes `k < i` (0-based), the probability of no shortage of class `i` in the
subproblem with products `k, …, i` decomposes according to the first product (from `i`
downwards) whose subproblem already has no shortage of class `i`. -/
theorem no_stockout_identity {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (y : Fin N → ℝ) (hy : 0 ≤ y) (k i : Fin N) (hki : k < i) :
    (Measure.pi ν).real {d | shortage y d i i = 0}
        + ∑ m ∈ Finset.univ.filter (fun m : Fin N => k ≤ m ∧ m < i),
            (Measure.pi ν).real {d | 0 < shortage y d (m + 1) i ∧ ShortVecZero y d m m i}
      = 1 - (Measure.pi ν).real {d | 0 < shortage y d k i} := by sorry

end BassokSubstitution
