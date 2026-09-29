import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- The instance of Theorem 2.31 (Zhang's inequality), p. 37, used inside the proof of Theorem
8.1: for every measurable `f : X → ℝ` with finite hinge and classification risk, the excess
classification risk is bounded by the excess (unrestricted) hinge risk,
`R_{L_class,P}(f) - R*_{L_class,P} ≤ R_{L_hinge,P}(f) - R*_{L_hinge,P}`. This is the chapter's own
formalization series's `01-loss-functions` mission's `zhang_inequality`, second clause, restated
locally per Hard Rule 9 rather than imported. -/
theorem theorem_2_31_instance_zhang {X : Type*} [MeasurableSpace X] (P : Measure (X × ℝ))
    [IsProbabilityMeasure P] (f : X → ℝ) (hf : Measurable f)
    (hInt1 : Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (f p.1)) P)
    (hInt2 : Integrable (fun p : X × ℝ => classLoss p.1 p.2 (f p.1)) P) :
    risk classLoss P f - bayesRisk classLoss P ≤
      risk hingeLoss P f - bayesRisk hingeLoss P := by sorry

end SupportVectorMachines.Classification
