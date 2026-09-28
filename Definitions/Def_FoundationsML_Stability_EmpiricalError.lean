import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss

namespace FoundationsML.Stability

/-- The empirical error of a hypothesis `h` on a sample `S = (z_1, …, z_m)` (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 334,
PDF p. 351): `R̂_S(h) = (1/m) ∑_{i=1}^m L_{z_i}(h)`. -/
noncomputable def EmpiricalError {X Y Y' : Type*} {m : ℕ} (L : Y' → Y → ℝ)
    (S : Fin m → X × Y) (h : X → Y') : ℝ :=
  (1 / (m : ℝ)) * ∑ i, Loss L h (S i)

end FoundationsML.Stability
