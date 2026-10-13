import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect

namespace BertsekasShreve.SemicontSelection

open MeasureTheory TopologicalSpace

/-- Proposition 7.31 (Bertsekas & Shreve, p. 148). Let `X`, `Y` be separable metrizable spaces,
`q(dy|x)` a continuous stochastic kernel on `Y` given `X`, and `f : X × Y → R*` Borel-measurable.
Let `λ(x) = ∫ f(x, y) q(dy|x)` (the extended integral (43) of Chapter 7, `∫ f⁺ − ∫ f⁻` with `∞ − ∞ = ∞`, which is `DupacovaWets.Consistency.expect`).
(a) If `f` is lower semicontinuous and bounded below, so is `λ`.
(b) If `f` is upper semicontinuous and bounded above, so is `λ`. -/
theorem prop7_31_semicontinuous_integral {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [SeparableSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (q : X → ProbabilityMeasure Y) (hq : Continuous q) (f : X × Y → EReal)
    (hf : @Measurable (X × Y) EReal (borel (X × Y)) _ f) :
    ((LowerSemicontinuous f ∧ ∃ b : ℝ, ∀ z, (b : EReal) ≤ f z) →
      LowerSemicontinuous (fun x => DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y))) ∧
      ∃ b : ℝ, ∀ x, (b : EReal) ≤ DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y))) ∧
    ((UpperSemicontinuous f ∧ ∃ b : ℝ, ∀ z, f z ≤ (b : EReal)) →
      UpperSemicontinuous (fun x => DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y))) ∧
      ∃ b : ℝ, ∀ x, DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y)) ≤ (b : EReal)) := by sorry

end BertsekasShreve.SemicontSelection

