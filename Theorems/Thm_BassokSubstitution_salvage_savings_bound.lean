import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- Lemma 5 (monotone form): for a class `i` (0-based), `s_1` times the no-stock-out
probability of Lemma 1 (with `k` the first product) minus the salvage-weighted sum of the same
probabilities is nondecreasing in the stock `y_i` on `[0, ∞)`. -/
theorem salvage_savings_bound {N : ℕ} [NeZero N] (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (y : Fin N → ℝ) (hy : 0 ≤ y) (i : Fin N) :
    MonotoneOn
      (fun t : ℝ =>
        M.s 0 * ((Measure.pi ν).real {d | shortage (Function.update y i t) d i i = 0}
            + ∑ m ∈ Finset.univ.filter (fun m : Fin N => m < i),
                (Measure.pi ν).real {d | 0 < shortage (Function.update y i t) d (m + 1) i ∧
                  ShortVecZero (Function.update y i t) d m m i})
          - (M.s i * (Measure.pi ν).real {d | shortage (Function.update y i t) d i i = 0}
            + ∑ m ∈ Finset.univ.filter (fun m : Fin N => m < i),
                M.s m * (Measure.pi ν).real {d | 0 < shortage (Function.update y i t) d (m + 1) i ∧
                  ShortVecZero (Function.update y i t) d m m i}))
      (Set.Ici 0) := by sorry

end BassokSubstitution
