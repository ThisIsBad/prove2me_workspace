import Mathlib
import Definitions.Def_FoundationsML_Regression_GeneralizationError
import Definitions.Def_FoundationsML_Regression_EmpiricalError
import Definitions.Def_FoundationsML_Regression_RademacherComplexity
import Definitions.Def_FoundationsML_Regression_EmpiricalRademacherComplexity

open MeasureTheory

namespace FoundationsML.Regression

/-- Theorem 11.3 (Rademacher complexity regression bounds; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 270, PDF p. 287). Let `L` be a
non-negative loss bounded by `M > 0` that is `µ`-Lipschitz in its first argument. Then, for
any `δ > 0`, with probability at least `1 − δ`, for all `h ∈ H`:
`E[L(h(x),y)] ≤ (1/m)∑L(h(x_i),y_i) + 2µ R_m(H) + M sqrt(log(1/δ)/(2m))`, and also
`E[L(h(x),y)] ≤ (1/m)∑L(h(x_i),y_i) + 2µ R̂_S(H) + 3M sqrt(log(2/δ)/(2m))`.

**Formalization Note.** `hH_meas`/`hL_meas` guard `GeneralizationError`'s Bochner integral
against trap 2, matching chunk `02-pac`'s precedent for this book's standing measurability
convention: without them, an adversarial `h ∈ H` could make `GeneralizationError` junk to `0`,
trivially satisfying the (already `≥0`, by `hLnn`) right-hand side for that `h`. -/
theorem rademacher_regression_bound
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M μ : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y')
    (hLb : ∀ y y', L y y' ≤ M) (hμ : 0 < μ)
    (hLlip : ∀ y' y1 y2, |L y1 y' - L y2 y'| ≤ μ * |y1 - y2|)
    (hL_meas : Measurable (Function.uncurry L))
    (H : Set (X → ℝ)) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            2 * μ * RademacherComplexity (Measure.map Prod.fst D) H m +
            M * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal ∧
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            2 * μ * EmpiricalRademacherComplexity H (fun i => (S i).1) +
            3 * M * Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Regression
