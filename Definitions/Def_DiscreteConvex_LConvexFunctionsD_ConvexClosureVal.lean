import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ConvexClosureValOn

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The convex closure `ḡ(x)` of `g`. -/
noncomputable def ConvexClosureVal (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ (S : Finset (V → ℤ)),
    (∀ y ∈ S, y ∈ DomZ g) ∧ L = ConvexClosureValOn g S x}

end DiscreteConvex.LConvexFunctionsD
