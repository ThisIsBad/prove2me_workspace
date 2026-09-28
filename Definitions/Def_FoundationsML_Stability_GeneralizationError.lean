import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss

open MeasureTheory

namespace FoundationsML.Stability

/-- The generalization error of a hypothesis `h`, for a loss function `L` and a distribution
`D` on labeled points (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd
ed., MIT Press 2018, p. 334, PDF p. 351): `R(h) = E_{z∼D}[L_z(h)]`. -/
noncomputable def GeneralizationError {X Y Y' : Type*} [MeasurableSpace (X × Y)]
    (D : Measure (X × Y)) (L : Y' → Y → ℝ) (h : X → Y') : ℝ :=
  ∫ z, Loss L h z ∂D

end FoundationsML.Stability
