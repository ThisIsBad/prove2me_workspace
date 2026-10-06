import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegerInterval

/-!
Boundedness of a discrete set, used in Theorem 3.29's "nonempty bounded effective domain"
hypothesis (Murota, *Discrete Convex Analysis*, SIAM 2003, p.97), in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `S` is **bounded**: contained in some finite integer interval. -/
def IsBoundedZ {n : ℕ} (S : Set (Fin n → ℤ)) : Prop :=
  ∃ lo hi : Fin n → ℤ, S ⊆ IntegerInterval lo hi

end DiscreteConvex.IntegralConvexityC
