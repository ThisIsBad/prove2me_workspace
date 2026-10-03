import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomZ

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (QSBw), the weaker variant of (QSB). -/
def QSBw (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p ∈ DomZ g, ∀ q ∈ DomZ g, max (g p) (g q) ≥ min (g (p ⊓ q)) (g (p ⊔ q))

end DiscreteConvex.LConvexFunctionsD
