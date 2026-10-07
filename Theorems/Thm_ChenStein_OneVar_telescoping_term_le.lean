import Mathlib
import Definitions.Def_ChenStein_OneVar_Setting

namespace ChenStein.OneVar

open MeasureTheory

/-- Arratia--Goldstein--Gordon (1989), §5, p. 22: one telescoping term. -/
theorem telescoping_term_le {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α))
    (hX01 : ∀ α ω, X α ω ≤ 1) (α β : I)
    (U : Ω → ℕ) (hUm : Measurable U) (f : ℕ → ℝ) (D : ℝ)
    (hD : ∀ w, |Δ f w| ≤ D) :
    ∫ ω, ((X α ω : ℝ) - p P X α) * (f (U ω + X β ω) - f (U ω)) ∂P
      ≤ D * (pab P X α β + p P X α * p P X β) := by sorry

end ChenStein.OneVar

