import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_ChenStein_Process_Setting

namespace ChenStein.Process

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem eq_15
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type*} (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α)) (hX01 : ∀ α ω, X α ω ≤ 1)
    (α β : I) {d : ℕ} (k : Fin d) (U : Ω → (Fin d → ℕ)) (hU : Measurable U)
    (f : (Fin d → ℕ) → ℝ) (F : ℝ) (hF : ∀ j, |f j| ≤ F) :
    ∫ ω, ((X α ω : ℝ) - p P X α) * (f (U ω + X β ω • e k) - f (U ω)) ∂P
      ≤ 2 * F * (pab P X α β + p P X α * p P X β) := by sorry

end ChenStein.Process

