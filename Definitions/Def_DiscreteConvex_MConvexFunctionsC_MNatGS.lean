import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_LinearWeight
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ArgMinOn

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M♮-GS[Z]), Eq. (6.64)-(6.65)-adjacent. -/
def MNatGS (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℝ, ∀ p0 q0 : ℝ, (∀ v, p v ≤ q v) → p0 ≤ q0 →
    ∀ x ∈ ArgMinOn (LinearWeight f (fun v => p v - p0)),
    (ArgMinOn (LinearWeight f (fun v => q v - q0))).Nonempty →
    ∃ y ∈ ArgMinOn (LinearWeight f (fun v => q v - q0)),
      (∀ v, p v = q v → y v ≥ x v) ∧ (p0 = q0 → ∑ v, y v ≤ ∑ v, x v)

end DiscreteConvex.MConvexFunctionsC
