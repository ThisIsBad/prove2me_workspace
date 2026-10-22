import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IntegralNeighborhoodFinset
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureValOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureVal

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is integrally convex, Eq. (3.71)-adjacent: the convex closure agrees with the local
convex closure taken only over each point's integral neighborhood. -/
def IsIntegrallyConvexFunction (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, ConvexClosureVal f p =
    ConvexClosureValOn f (Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p)) p

end DiscreteConvex.MConvexFunctionsC
