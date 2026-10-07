import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Structural

/-- **Theorem 12, part 4** (Bartlett–Mendelson, JMLR 3 (2002), p. 469): if `φ : ℝ → ℝ` is
Lipschitz with constant `L_φ` and `φ(0) = 0`, then `R_n(φ ∘ F) ≤ 2 L_φ R_n(F)`, where
`φ ∘ F = {φ ∘ f | f ∈ F}`. -/
theorem theorem_12_part_4 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F : Set (X → ℝ)) (φ : ℝ → ℝ) (Lφ : NNReal)
    (hφ : LipschitzWith Lφ φ) (hφ0 : φ 0 = 0) :
    RadGauss.RiskBound.rademacherComplexity μ n ((fun f => φ ∘ f) '' F) ≤
      2 * (Lφ : ℝ≥0∞) * RadGauss.RiskBound.rademacherComplexity μ n F := by sorry

end RadGauss.Structural

