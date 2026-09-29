import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_GeneralizationError
import Definitions.Def_FoundationsML_RademacherVC_EmpiricalError
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim

open MeasureTheory

namespace FoundationsML.RademacherVC

/-- Corollary 3.19 (VC-dimension generalization bound; goal; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 42, PDF p. 59).
Let `H` be a family of functions taking values in `{−1,+1}` (here: `Bool`) with VC-dimension
`d`. Then, for any `δ > 0`, with probability at least `1 − δ`, the following holds for all
`h ∈ H`:
`R(h) ≤ R̂_S(h) + sqrt(2d log(em/d)/m) + sqrt(log(1/δ)/(2m))`. -/
theorem vc_dimension_generalization_bound
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Set (X → Bool)) (d : ℕ) (hH : HasVCDim H d) (c : X → Bool)
    (m : ℕ) (hm : d ≤ m) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt (2 * d * Real.log (Real.exp 1 * m / d) / m) +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.RademacherVC

