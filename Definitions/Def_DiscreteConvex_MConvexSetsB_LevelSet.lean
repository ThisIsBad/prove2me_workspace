import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SortedValues

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.103, Eq. (4.4): the level sets `Uᵢ` used in
the Lovász extension, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

open Classical in
/-- The `i`-th level set `Uᵢ = \{v ∈ V : p(v) ≥ p̂ᵢ\}` (1-indexed, Eq. (4.4)); `i = 0` is unused
and returns `∅` by the `getD` default. -/
noncomputable def LevelSet {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) (i : ℕ) :
    Finset V :=
  Finset.univ.filter (fun v => (SortedValues p).getD (i - 1) 0 ≤ p v)

end DiscreteConvex.MConvexSetsB
