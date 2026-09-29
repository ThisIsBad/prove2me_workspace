import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- Lemma 2 (monotone form): for classes `k < i` (0-based), the left-hand side of Lemma 1 is a
nondecreasing function of the stock `y_i` of product `i` on `[0, ∞)`, the other stocks being
fixed. -/
theorem no_stockout_monotone {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (y : Fin N → ℝ) (hy : 0 ≤ y) (k i : Fin N) (hki : k < i) :
    MonotoneOn
      (fun t : ℝ =>
        (Measure.pi ν).real {d | shortage (Function.update y i t) d i i = 0}
          + ∑ m ∈ Finset.univ.filter (fun m : Fin N => k ≤ m ∧ m < i),
              (Measure.pi ν).real {d | 0 < shortage (Function.update y i t) d (m + 1) i ∧
                ShortVecZero (Function.update y i t) d m m i})
      (Set.Ici 0) := by sorry

end BassokSubstitution
