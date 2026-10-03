import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomZ

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SSQSBw), the weaker variant of (SSQSB). -/
def SSQSBw (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p ∈ DomZ g, ∀ q ∈ DomZ g,
    max (g p) (g q) > min (g (p ⊓ q)) (g (p ⊔ q)) ∨
      (g p = g q ∧ g p = g (p ⊓ q) ∧ g p = g (p ⊔ q))

end DiscreteConvex.LConvexFunctionsD
