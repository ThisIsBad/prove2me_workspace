import Mathlib

namespace FoundationsML.MultiClass

/-- The margin `ρ_h(x,y)` of a multi-class scoring function `h : X × Y → ℝ` at a labeled
example `(x,y)` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 215, PDF p. 232): `ρ_h(x,y) = h(x,y) − max_{y'≠y} h(x,y')`. The hypothesis
`h` misclassifies `(x,y)` iff `ρ_h(x,y) ≤ 0`.

**Formalization Note.** `⨆ y' ∈ {y' | y' ≠ y}, h (x, y')` is the real supremum over the
(possibly infinite) set of labels other than `y`; for a finite `Y` with at least two elements
this equals the book's `max_{y'≠y}`, matching trap 5's guard whenever a consuming theorem
supplies `2 ≤ Fintype.card Y` (or an analogous nontriviality hypothesis). -/
noncomputable def MarginFunction {X Y : Type*} (h : X × Y → ℝ) (x : X) (y : Y) : ℝ :=
  h (x, y) - ⨆ y' ∈ {y' : Y | y' ≠ y}, h (x, y')

end FoundationsML.MultiClass
