import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_HoleFree

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.91, Eq. (3.53): a translation-invariant family
of hole-free discrete sets, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `F` satisfies (3.53): every `S ∈ F` is hole free, and `F` is closed under translation by
any integer vector (`x - S ∈ F` for all `x ∈ Zⱽ`). -/
def IsTranslInvariantHoleFreeFamily {V : Type*} (F : Set (Set (V → ℤ))) : Prop :=
  ∀ S ∈ F, HoleFree S ∧ ∀ x : V → ℤ, (fun y => x - y) '' S ∈ F

end DiscreteConvex.IntegralConvexityB
