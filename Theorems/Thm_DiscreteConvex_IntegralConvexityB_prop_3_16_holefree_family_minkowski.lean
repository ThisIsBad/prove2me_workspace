import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsTranslInvariantHoleFreeFamily
import Definitions.Def_DiscreteConvex_IntegralConvexityB_ConvexClosureSet
import Definitions.Def_DiscreteConvex_IntegralConvexityB_MinkowskiSumZ
import Definitions.Def_DiscreteConvex_IntegralConvexityB_EmbedZR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.91, Proposition 3.16, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

open scoped Pointwise

/-- **Proposition 3.16.** Suppose a family `F` of sets of integer points satisfies (3.53).
Then (a) `∀S1,S2∈F: S1∩S2=∅ ⟹ S̄1∩S̄2=∅` is equivalent to (b) `∀S1,S2∈F:
S1+S2 = \{x ∈ Zⱽ | x ∈ S̄1+S̄2\}`. -/
theorem prop_3_16_holefree_family_minkowski {V : Type*} [Fintype V] [DecidableEq V]
    (F : Set (Set (V → ℤ))) (hF : IsTranslInvariantHoleFreeFamily F) :
    (∀ S1 ∈ F, ∀ S2 ∈ F, S1 ∩ S2 = ∅ → ConvexClosureSet S1 ∩ ConvexClosureSet S2 = ∅) ↔
      (∀ S1 ∈ F, ∀ S2 ∈ F,
        MinkowskiSumZ S1 S2 =
          {x : V → ℤ | EmbedZR x ∈ ConvexClosureSet S1 + ConvexClosureSet S2}) := by sorry

end DiscreteConvex.IntegralConvexityB
