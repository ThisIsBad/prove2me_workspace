import Mathlib

namespace FoundationsML.MultiClass

/-- The margin loss function `Φ_ρ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 5.5, referenced at p. 215, PDF p. 232, and
restated locally here since a draft module cannot import chunk `05-svm`'s own draft copy):
`Φ_ρ(x) = 1` if `x ≤ 0`, `1 − x/ρ` if `0 ≤ x ≤ ρ`, and `0` if `x ≥ ρ`. -/
noncomputable def MarginLossFunction (ρ : ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 1 else if x ≤ ρ then 1 - x / ρ else 0

end FoundationsML.MultiClass
