import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process

namespace KingmanSubadditive.Continuous

open MeasureTheory

/-- Kingman, §1.4, proof of Theorem 4, p. 889, the sandwich display.
Formalization Note: `n ≥ 1` and `n < t < n+1` keep every coordinate valid;
finite oscillation at this sample point allows conversion from `ENNReal`
to real. The printed strict upper sign is corrected to `≤`. -/
theorem sandwich {S : Type*} [MeasurableSpace S]
    (P : Measure S) (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hnt : (n : ℝ) < t) (htn : t < (n : ℝ) + 1)
    (ω : S)
    (hfinite : oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω < ⊤) :
    x 0 ((n : ℝ) + 1) ω -
        (oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω).toReal ≤
      x 0 t ω ∧
      x 0 t ω ≤ x 0 n ω +
        (oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω).toReal := by sorry

end KingmanSubadditive.Continuous

