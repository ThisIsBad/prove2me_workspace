import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_ConvexClosureSet
import Definitions.Def_DiscreteConvex_IntegralConvexityB_EmbedZR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.90, Eq. (3.50): the hole-free property, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `S` is **hole free** (Eq. (3.50)): `S = S̄ ∩ Zⱽ`, i.e. every integer point of `S`'s convex
hull already belongs to `S`. -/
def HoleFree {V : Type*} (S : Set (V → ℤ)) : Prop :=
  ∀ x : V → ℤ, x ∈ S ↔ EmbedZR x ∈ ConvexClosureSet S

end DiscreteConvex.IntegralConvexityB
