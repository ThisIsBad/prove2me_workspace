import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_RiskBasics
import Definitions.Def_SupportVectorMachines_LossFunctions_ClassificationLosses

open MeasureTheory

namespace SupportVectorMachines.LossFunctions

/-- Theorem 2.31 (Zhang's inequality), p. 37: given a distribution `P` on `X × Y` (`Y := {-1,1}`)
with `η(x) := P(y=1|x)` and Bayes classifier `f*_{L_class,P}(x) := sign(2η(x)-1)`:

* for every measurable `f : X → [-1,1]` with finite hinge risk,
  `R_{L_hinge,P}(f) - R*_{L_hinge,P} = ∫_X |f(x) - f*_{L_class,P}(x)| · |2η(x) - 1| dP_X(x)`
  (an exact equality);
* for every measurable `f : X → ℝ` with finite hinge and classification risk,
  `R_{L_class,P}(f) - R*_{L_class,P} ≤ R_{L_hinge,P}(f) - R*_{L_hinge,P}`.

`η` is represented via its defining disintegration property: for every measurable `A ⊆ X`,
`P(A × {1}) = ∫_{x ∈ A} η(x) dP_X(x)`, where `P_X := P.map Prod.fst` is the `X`-marginal. The
finite-risk hypotheses guard the real-valued (junk-at-non-integrable) Bochner integral used for
`risk`/`bayesRisk`: the book's risks are extended-real-valued and the difference is understood
whenever the risks involved are finite, which is automatic for `L_class` (bounded by 1) and for
`L_hinge` on `f` valued in `[-1,1]` (bounded by 2), and is stated explicitly for the general `f`
of the second assertion. -/
theorem zhang_inequality {X : Type*} [MeasurableSpace X] (P : Measure (X × ℝ))
    [IsProbabilityMeasure P] (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) (η : X → ℝ)
    (hη : ∀ A, MeasurableSet A →
      (P (A ×ˢ ({1} : Set ℝ))).toReal = ∫ x in A, η x ∂(P.map Prod.fst)) :
    (∀ f : X → ℝ, Measurable f → (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) →
        Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (f p.1)) P →
        risk hingeLoss P f - bayesRisk hingeLoss P =
          ∫ x, |f x - bayesClassifier η x| * |2 * η x - 1| ∂(P.map Prod.fst)) ∧
      ∀ f : X → ℝ, Measurable f →
        Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (f p.1)) P →
        Integrable (fun p : X × ℝ => classLoss p.1 p.2 (f p.1)) P →
        risk classLoss P f - bayesRisk classLoss P ≤
          risk hingeLoss P f - bayesRisk hingeLoss P := by sorry

end SupportVectorMachines.LossFunctions
