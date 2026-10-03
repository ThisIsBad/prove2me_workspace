import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.103, Eq. (4.4): the distinct values of a
vector `p`, sorted in decreasing order, in `DiscreteConvex.MConvexSetsB`. Supports the Lovász
extension (Eq. (4.6), Proposition 4.5, Theorem 4.16).
-/

namespace DiscreteConvex.MConvexSetsB

open Classical in
/-- The distinct values of `p : V → R`, sorted in decreasing order: `p̂₁ > p̂₂ > ⋯ > p̂ₘ`
(Eq. (4.4)). -/
noncomputable def SortedValues {V : Type*} [Fintype V] (p : V → ℝ) : List ℝ :=
  (Finset.image p Finset.univ).sort (· ≥ ·)

end DiscreteConvex.MConvexSetsB
