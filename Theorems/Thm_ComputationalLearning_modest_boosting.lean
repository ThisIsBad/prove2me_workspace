import Definitions.Def_ComputationalLearning_Boosting

open MeasureTheory ProbabilityTheory


namespace ComputationalLearning

/-- **Lemma 4.1** (p. 82). Let `g(β) = 3β² − 2β³`. Let the distributions `D`, `D₂` and `D₃` be as
defined in §4.3.1 (`D₂` filters `D` through `h₁`, `D₃` conditions `D` on `h₁ ≠ h₂`), and let
`h₁, h₂, h₃` satisfy `error_D(h₁) ≤ β`, `error_{D₂}(h₂) ≤ β` and `error_{D₃}(h₃) ≤ β`. Then, for
`h = majority(h₁, h₂, h₃)`, `error_D(h) ≤ g(β)`. Stated for `0 ≤ β ≤ 1/2` and measurable
`c, h₁, h₂, h₃`; when a conditioning event is null the corresponding filtered measure is the zero
measure (or has mass `1/2`), and the bound still holds. -/
theorem modest_boosting {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c h₁ h₂ h₃ : X → Bool) (hc : Measurable c) (h₁m : Measurable h₁) (h₂m : Measurable h₂)
    (h₃m : Measurable h₃) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (e₁ : errorOf D c h₁ ≤ β) (e₂ : errorOf (filtered2 D c h₁) c h₂ ≤ β)
    (e₃ : errorOf (filtered3 D h₁ h₂) c h₃ ≤ β) :
    errorOf D c (majority3 h₁ h₂ h₃) ≤ boostFun β := by sorry

end ComputationalLearning

