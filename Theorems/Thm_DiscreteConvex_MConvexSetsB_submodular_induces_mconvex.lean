import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.109-110, Proposition 4.14, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.14 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.109-110). See the item's
`natural_language_statement` for the full statement. -/
theorem submodular_induces_mconvex {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (hInt : IsIntegerValued ρ) :
    ExchangeAxiomB {x : V → ℤ | (fun v => (x v : ℝ)) ∈ BasePolyhedron ρ} ∧
      ({x : V → ℤ | (fun v => (x v : ℝ)) ∈ BasePolyhedron ρ}).Nonempty ∧
      (∀ X : Finset V, ρ X = ⨆ x ∈ BasePolyhedron ρ, (((∑ v ∈ X, x v : ℝ)) : WithTop ℝ)) := by sorry

end DiscreteConvex.MConvexSetsB
