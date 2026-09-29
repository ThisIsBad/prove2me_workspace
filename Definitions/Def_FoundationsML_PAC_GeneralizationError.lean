import Mathlib

open MeasureTheory

namespace FoundationsML.PAC

/-- The generalization error (risk) of a hypothesis `h : X → Y` against a target concept
`c : X → Y` and an underlying distribution `D` on `X` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 2.1, p. 10, PDF p. 27):
`R(h) = P_{x∼D}[h(x) ≠ c(x)]`. -/
noncomputable def GeneralizationError {X Y : Type*} [MeasurableSpace X]
    (D : Measure X) (c h : X → Y) : ℝ :=
  (D {x | h x ≠ c x}).toReal

end FoundationsML.PAC
