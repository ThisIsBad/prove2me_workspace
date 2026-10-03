import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SortedValues
import Definitions.Def_DiscreteConvex_MConvexSetsB_LevelSet
import Definitions.Def_DiscreteConvex_MConvexSetsB_ScalarWithTop

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.103, Eq. (4.6): the Lovász extension of a
set function, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

open Classical in
/-- The **Lovász extension** `ρ̂ : Rⱽ → R ∪ \{±∞\}` of a set function `ρ`, Eq. (4.6): the linear
interpolation `ρ̂(p) = Σᵢ₌₁^{m-1} (p̂ᵢ - p̂ᵢ₊₁) ρ(Uᵢ) + p̂ₘ ρ(Uₘ)` with respect to the
representation (4.5) of `p` as a combination of the level-set indicators `χ_{Uᵢ}`. -/
noncomputable def LovaszExtension {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (p : V → ℝ) : WithTop ℝ :=
  let vals := SortedValues p
  let m := vals.length
  (∑ i ∈ Finset.range (m - 1),
      ScalarWithTop (vals.getD i 0 - vals.getD (i + 1) 0) (ρ (LevelSet p (i + 1)))) +
    ScalarWithTop (vals.getD (m - 1) 0) (ρ (LevelSet p m))

end DiscreteConvex.MConvexSetsB
