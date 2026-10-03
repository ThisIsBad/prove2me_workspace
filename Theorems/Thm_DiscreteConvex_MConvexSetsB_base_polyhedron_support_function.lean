import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSetsB_LovaszExtension
import Definitions.Def_DiscreteConvex_MConvexSetsB_SortedValues
import Definitions.Def_DiscreteConvex_MConvexSetsB_LevelSet
import Definitions.Def_DiscreteConvex_MConvexSetsB_ScalarWithTop

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.105, Proposition 4.5, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.5 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.105). See the item's
`natural_language_statement` for the full statement. -/
theorem base_polyhedron_support_function {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (p : V → ℝ) :
    (⨆ x ∈ BasePolyhedron ρ, (((∑ v, p v * x v : ℝ)) : WithTop ℝ)) = LovaszExtension ρ p := by sorry

end DiscreteConvex.MConvexSetsB
