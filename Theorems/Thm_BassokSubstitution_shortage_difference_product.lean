import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- Lemma 3: for products `j < i` (0-based), with independent demand classes, the difference of
the two "salvage" probabilities factors as a product. Empty vector conditions (when `i` is the
last class) are vacuously true. -/
theorem shortage_difference_product {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (y : Fin N → ℝ) (hy : 0 ≤ y) (j i : Fin N) (hji : j < i) :
    (Measure.pi ν).real
        {d | ¬ ShortVecZero y d (j + 1) i (N - 1) ∧ ShortVecZero y d j i (N - 1)}
      - (Measure.pi ν).real
        {d | ¬ ShortVecZero y d (j + 1) (i + 1) (N - 1) ∧ ShortVecZero y d j (i + 1) (N - 1)}
      = (Measure.pi ν).real {d | 0 < shortage y d (j + 1) i ∧ ShortVecZero y d j j i}
        * (Measure.pi ν).real {d | ShortVecZero y d (i + 1) (i + 1) (N - 1)} := by sorry

end BassokSubstitution
