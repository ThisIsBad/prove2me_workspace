import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.108-109, Eq. (4.25): the submodular set
function induced by an M-convex set, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The set function `ρ(X) = sup\{x(X) : x ∈ B\}` induced by a set `B ⊆ Zⱽ` of integer
vectors, Eq. (4.25); used in Proposition 4.13 to recover the submodular function associated
with an M-convex set. -/
noncomputable def InducedRho {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ)) :
    Finset V → WithTop ℝ :=
  fun X => sSup ((fun x : V → ℤ => (((∑ v ∈ X, x v : ℤ) : ℝ) : WithTop ℝ)) '' B)

end DiscreteConvex.MConvexSetsB
