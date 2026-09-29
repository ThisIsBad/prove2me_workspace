import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_FacetHyperplanes

open Pointwise

namespace LovaszSchrijver.OddHole

/-- Lemma 1.3 (p. 171): for every (closed) convex cone `K ⊆ Q` and every `1 ≤ i ≤ n`,
`N(K) ⊆ (K ∩ Hᵢ) + (K ∩ Gᵢ)`. -/
theorem N_subset_H_add_G {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKQ : K ⊆ Q ι)
    (i : ι) :
    N K ⊆ (K ∩ Hplane i) + (K ∩ Gplane i) := by sorry

end LovaszSchrijver.OddHole
