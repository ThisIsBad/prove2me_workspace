import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureValOn

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The convex closure `f̄ : Rⱽ → R ∪ {±∞}` of `f`, Eq. (3.57)-adjacent: the infimum over convex
combinations of points of `dom f`. -/
noncomputable def ConvexClosureVal (f : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ (S : Finset (V → ℤ)),
    (∀ y ∈ S, y ∈ DomZ f) ∧ L = ConvexClosureValOn f S x}

end DiscreteConvex.MConvexFunctionsC
