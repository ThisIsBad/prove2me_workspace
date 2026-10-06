import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_LovaszExtension
import Definitions.Def_DiscreteConvex_MConvexSetsB_SortedValues
import Definitions.Def_DiscreteConvex_MConvexSetsB_LevelSet
import Definitions.Def_DiscreteConvex_MConvexSetsB_ScalarWithTop
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsConvexWithTop


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.111, Theorem 4.16, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Theorem 4.16 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.111). See the item's
`natural_language_statement` for the full statement. -/
theorem lovasz_convex_iff_submodular {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ0 : ρ ∅ = 0) (hρV : ρ Finset.univ ≠ ⊤) :
    (∀ X Y : Finset V, ρ X + ρ Y ≥ ρ (X ∪ Y) + ρ (X ∩ Y)) ↔ IsConvexWithTop (LovaszExtension ρ) := by sorry

end DiscreteConvex.MConvexSetsB

