import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IndicatorVec

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The set function `ρ_g(X) = g(χ_X)` induced by a positively homogeneous integer-domain
function. -/
def InducedRhoZ (g : (V → ℤ) → WithTop ℝ) (X : Finset V) : WithTop ℝ := g (IndicatorVec X)

end DiscreteConvex.LConvexFunctionsD
