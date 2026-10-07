import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_PhiLossPointwise

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- The expected Φ-loss of a real-valued scoring function `h : X → ℝ`,
`L_Φ(h) = E_{x∼D_X}[η(x) Φ(−h(x)) + (1 − η(x)) Φ(h(x))]` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Eq. (4.10), p. 75, PDF p. 92). -/
noncomputable def ExpectedPhiLoss {X : Type*} [MeasurableSpace X]
    (DX : Measure X) (η : X → ℝ) (Φ : ℝ → ℝ) (h : X → ℝ) : ℝ :=
  ∫ x, PhiLossPointwise η Φ x (h x) ∂DX

end FoundationsML.ModelSelection
