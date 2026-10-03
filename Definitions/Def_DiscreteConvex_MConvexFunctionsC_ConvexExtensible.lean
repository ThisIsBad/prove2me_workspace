import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureVal

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is convex extensible, Eq. (3.57): its convex closure agrees with `f` on `Zⱽ`. -/
def ConvexExtensible (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℤ, ConvexClosureVal f (fun v => (x v : ℝ)) = f x

end DiscreteConvex.MConvexFunctionsC
