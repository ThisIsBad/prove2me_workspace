import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntPts
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
open scoped Pointwise


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.115-116, Theorem 4.23, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Theorem 4.23 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.115-116). See the item's
`natural_language_statement` for the full statement. -/
theorem submodular_base_polyhedron_minkowski_sum {V : Type*} [Fintype V] [DecidableEq V]
    (ρ1 ρ2 : Finset V → WithTop ℝ) (hρ1 : SubmodularSetFunction ρ1) (hρ2 : SubmodularSetFunction ρ2)
    (B1 B2 : Set (V → ℤ)) (hExc1 : ExchangeAxiomB B1) (hExc2 : ExchangeAxiomB B2)
    (hB1ne : B1.Nonempty) (hB2ne : B2.Nonempty) :
    (BasePolyhedron ρ1 + BasePolyhedron ρ2 = BasePolyhedron (fun X => ρ1 X + ρ2 X)) ∧
    (IsIntegerValued ρ1 → IsIntegerValued ρ2 →
      (BasePolyhedron ρ1 ∩ IntPts) + (BasePolyhedron ρ2 ∩ IntPts) =
        BasePolyhedron (fun X => ρ1 X + ρ2 X) ∩ IntPts) ∧
    (ExchangeAxiomB (B1 + B2) ∧ (B1 + B2).Nonempty ∧
      convexHull ℝ (IntEmbed (B1 + B2)) = convexHull ℝ (IntEmbed B1) + convexHull ℝ (IntEmbed B2)) := by sorry

end DiscreteConvex.MConvexSetsB

