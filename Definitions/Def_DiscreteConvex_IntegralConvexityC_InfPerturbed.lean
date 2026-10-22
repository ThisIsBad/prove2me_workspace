import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ToEReal3

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, citing `inf f[-p]`: the infimum value of a
linearly perturbed function, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `inf f[-p] = inf_x \{f(x) - ⟨p,x⟩\}`, valued in `EReal`. -/
noncomputable def InfPerturbed {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (p : Fin n → ℝ) : EReal :=
  sInf {v : EReal | ∃ x : Fin n → ℤ, v = ToEReal3 (f x) - ((∑ i, p i * (x i : ℝ) : ℝ) : EReal)}

end DiscreteConvex.IntegralConvexityC
