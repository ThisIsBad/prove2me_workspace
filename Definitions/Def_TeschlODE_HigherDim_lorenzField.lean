import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §8.2, p. 234, (8.13): the Lorenz vector field on `ℝ³ ∋ (x, y, z)`,
`ẋ = -σ(x - y)`, `ẏ = r x - y - x z`, `ż = x y - b z`. -/
noncomputable def lorenzField (σ r b : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[-σ * (v 0 - v 1), r * v 0 - v 1 - v 0 * v 2, v 0 * v 1 - b * v 2]

end TeschlODE.HigherDim
