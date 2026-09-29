import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_GeneralizationError
import Definitions.Def_FoundationsML_ModelSelection_EmpiricalError

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- Proposition 4.1 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*,
2nd ed., MIT Press 2018, p. 62, PDF p. 79). Let `hERM` be the hypothesis returned by empirical
risk minimization over a nonempty hypothesis set `H`: `hERM S ∈ H` and `hERM S` minimizes the
empirical error `R̂_S(·)` over `H`, for every sample `S`. Then, for any `ε`,
`P[R(h_S^ERM) − inf_{h∈H} R(h) > ε] ≤ P[sup_{h∈H} |R(h) − R̂_S(h)| > ε/2]`, the probability
taken over the draw of `S` from `D^m`. -/
theorem erm_bound {X Y : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c : X → Y) (H : Set (X → Y)) (hH : H.Nonempty) (m : ℕ)
    (hERM : (Fin m → X) → (X → Y))
    (hERM_mem : ∀ S, hERM S ∈ H)
    (hERM_min : ∀ S, ∀ h ∈ H, EmpiricalError S c (hERM S) ≤ EmpiricalError S c h)
    (ε : ℝ) :
    (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c (hERM S) -
        sInf (GeneralizationError D c '' H) > ε}).toReal ≤
    (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | (⨆ h ∈ H, |GeneralizationError D c h - EmpiricalError S c h|) > ε / 2}
      ).toReal := by sorry

end FoundationsML.ModelSelection
