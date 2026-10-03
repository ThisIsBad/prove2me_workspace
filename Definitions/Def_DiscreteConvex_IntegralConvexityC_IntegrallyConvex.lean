import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ConvexClosure
import Definitions.Def_DiscreteConvex_IntegralConvexityC_LocalConvexExtension

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.94, Eq. (3.64): integral convexity of a
function, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `f` is **integrally convex** if `f̃(x) = f̄(x)` for all `x ∈ Rⁿ` (Eq. (3.64)). -/
noncomputable def IntegrallyConvex {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : Fin n → ℝ, LocalConvexExtension f x = ConvexClosure f x

end DiscreteConvex.IntegralConvexityC
