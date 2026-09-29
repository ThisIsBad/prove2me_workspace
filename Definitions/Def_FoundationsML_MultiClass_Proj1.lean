import Mathlib

namespace FoundationsML.MultiClass

/-- The projection `Π_1(H)` of a family `H` of multi-class scoring functions
`h : X × Y → ℝ` onto its first coordinate (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, p. 217, PDF p. 234):
`Π_1(H) = {x ↦ h(x,y) : y ∈ Y, h ∈ H}`. -/
def Proj1 {X Y : Type*} (H : Set (X × Y → ℝ)) : Set (X → ℝ) :=
  {g | ∃ h ∈ H, ∃ y : Y, g = fun x => h (x, y)}

end FoundationsML.MultiClass
