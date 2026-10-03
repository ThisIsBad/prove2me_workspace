import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_FromEReal
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateFromZE

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f(x) = sup{⟨p,x⟩ - g(p) | p ∈ Zⱽ}`, the mixed real-primal/integer-dual conjugate, Eq.
(10.76): `f ∈ M[R→R|Z]` (dual integral) exactly when `f` arises this way from some `g`. -/
noncomputable def ConjugateFromZ (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : WithTop ℝ :=
  FromEReal (ConjugateFromZE g x)

end DiscreteConvex.AlgorithmsC
