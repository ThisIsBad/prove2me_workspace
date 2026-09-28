import Mathlib

namespace FoundationsML.Stability

/-- The loss of a hypothesis `h` at a labeled point `z = (x, y)` (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 333-334, PDF p.
350-351): for a loss function `L : Y' × Y → ℝ_+`, `L_z(h) = L(h(x), y)`. -/
noncomputable def Loss {X Y Y' : Type*} (L : Y' → Y → ℝ) (h : X → Y') (z : X × Y) : ℝ :=
  L (h z.1) z.2

end FoundationsML.Stability
