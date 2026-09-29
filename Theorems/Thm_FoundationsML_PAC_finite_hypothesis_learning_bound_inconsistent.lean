import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

open MeasureTheory

namespace FoundationsML.PAC

/-- Theorem 2.13 (Learning bound — finite `H`, inconsistent case; goal; Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
p. 20, PDF p. 37). Let `H` be a finite hypothesis set of functions `X → Bool` and `c`
a target concept. Then, for any `δ > 0`, with probability at least `1 − δ` over an
i.i.d. sample `S ∼ D^m`, simultaneously for every `h ∈ H`,
`R(h) ≤ R̂_S(h) + sqrt((log|H| + log(2/δ)) / (2m))`.

**Formalization note.** Carries the book's standing measurability hypothesis (Definition 2.1,
footnote 2, p. 11) on `c` and on every `h ∈ H`. -/
theorem finite_hypothesis_learning_bound_inconsistent
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Finset (X → Bool)) (c : X → Bool)
    (hc_meas : Measurable c) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt ((Real.log (H.card : ℝ) + Real.log (2 / δ)) / (2 * m))}).toReal := by sorry

end FoundationsML.PAC

