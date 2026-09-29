import Mathlib

namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), p. 213: the continuous convex function `j(x) = (1/2)‖x‖²`,
regarded as a (finite-valued) function `V → (−∞, +∞]`. -/
noncomputable def halfSqNorm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x : V) :
    EReal :=
  ((‖x‖ ^ 2 / 2 : ℝ) : EReal)

end RockafellarMaxMono.Shared
