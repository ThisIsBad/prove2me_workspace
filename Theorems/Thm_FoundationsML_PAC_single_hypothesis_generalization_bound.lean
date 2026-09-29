import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

open MeasureTheory

namespace FoundationsML.PAC

/-- Corollary 2.11 (Generalization bound — single hypothesis; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 19, PDF p. 36).
Fix a hypothesis `h : X → Bool` and a target concept `c : X → Bool`. Then, for any `δ > 0`,
with probability at least `1 − δ` over an i.i.d. sample `S ∼ D^m`,
`R(h) ≤ R̂_S(h) + sqrt(log(2/δ) / (2m))`.

**Formalization note.** Carries the book's standing measurability hypothesis (Definition 2.1,
footnote 2, p. 11) on `c` and `h`. -/
theorem single_hypothesis_generalization_bound
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c h : X → Bool) (hc_meas : Measurable c) (hh_meas : Measurable h)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c h ≤
        EmpiricalError S c h + Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.PAC

