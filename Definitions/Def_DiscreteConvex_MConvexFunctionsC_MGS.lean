import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_LinearWeight
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ArgMinOn

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M-GS[Z]), Eq. (6.60). -/
def MGS (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℝ, (∀ v, p v ≤ q v) → ∀ x ∈ ArgMinOn (LinearWeight f p),
    (ArgMinOn (LinearWeight f q)).Nonempty →
    ∃ y ∈ ArgMinOn (LinearWeight f q), ∀ v, p v = q v → y v ≥ x v

end DiscreteConvex.MConvexFunctionsC
