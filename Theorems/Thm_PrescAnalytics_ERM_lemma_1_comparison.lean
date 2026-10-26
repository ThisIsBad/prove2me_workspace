import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Basic

namespace PrescAnalytics.ERM

open MeasureTheory

/-- Lemma 1 (pp. 39–40), multivariate comparison lemma. If the cost `c(z; y)` is `L`-Lipschitz in
the decision `z ∈ ℝ^d` with respect to the `∞`-norm, uniformly over `y`, then for the cost class
`𝒢 = {(x, y) ↦ c(f(x); y) : f ∈ F}`:
(i) on every sample `S_N`, `ℜ̂_N(𝒢; S_N) ≤ L ℜ̂_N(F; S_N^x)`;
(ii) for i.i.d. sampling from `μ`, `ℜ_N(𝒢) ≤ L ℜ_N(F)`, where `ℜ_N(F)` samples only the
covariates, i.e. from the marginal `μ_X` of `μ`. Part (ii) carries the measurability conventions
(measurable rules, pointwise separable class, measurable cost) under which the expectations exist. -/
theorem lemma_1_comparison {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {d : ℕ}
    (F : Set (X → Fin d → ℝ)) (c : (Fin d → ℝ) → Y → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖) :
    (∀ (N : ℕ) (s : Fin N → X × Y),
        empRademacherR (costClass c F) s ≤ (L : EReal) * empRademacher F (fun i => (s i).1)) ∧
    (∀ (μ : Measure (X × Y)) [IsProbabilityMeasure μ] (N : ℕ),
        (∀ f ∈ F, Measurable f) → IsPointwiseSeparable F → Measurable (Function.uncurry c) →
        margRademacherR μ N (costClass c F) ≤
          ENNReal.ofReal L * margRademacher (μ.map Prod.fst) N F) := by sorry

end PrescAnalytics.ERM

