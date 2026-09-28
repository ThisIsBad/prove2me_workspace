import Mathlib
import Definitions.Def_CubicNewton_Shared_cubicModel

namespace CubicNewton.Shared

/-- `T` is a cubic-regularized Newton step from `x` with parameter `M` (Nesterov–Polyak 2006,
p. 181, Eq. (2.4)): `T` is a **global** minimizer of `y ↦ cubicModel g H M x y` over the whole
space. The paper's `T_M(x)` is any element of this set of global minima. -/
def IsCubicStep {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ y, cubicModel g H M x T ≤ cubicModel g H M x y

end CubicNewton.Shared
