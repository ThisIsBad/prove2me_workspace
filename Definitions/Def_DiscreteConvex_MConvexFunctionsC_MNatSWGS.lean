import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_LinearWeight
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ArgMinOn

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M♮-SWGS[Z]). -/
def MNatSWGS (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, ∀ x ∈ ArgMinOn (LinearWeight f p), ∀ u : V,
    (∀ alpha : ℝ, 0 ≤ alpha →
        x ∈ ArgMinOn (LinearWeight f (fun v => p v + (if v = u then alpha else 0)))) ∨
    (∃ alpha : ℝ, 0 ≤ alpha ∧
      ∃ y ∈ ArgMinOn (LinearWeight f (fun v => p v + (if v = u then alpha else 0))),
        y u = x u - 1 ∧ ∀ v, v ≠ u → y v ≥ x v)

end DiscreteConvex.MConvexFunctionsC
