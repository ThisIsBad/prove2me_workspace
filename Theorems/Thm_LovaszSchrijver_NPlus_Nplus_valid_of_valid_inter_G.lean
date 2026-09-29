import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_MatrixCone

namespace LovaszSchrijver.NPlus

theorem Nplus_valid_of_valid_inter_G {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKQ : K ⊆ Q) (hKc : IsClosed K)
    (a : Option ι → ℝ) (ha : ∀ i : ι, a (some i) ≤ 0) (ha₀ : 0 ≤ a none)
    (hvalid : ∀ i : ι, a (some i) < 0 → ∀ x ∈ K ∩ G i, 0 ≤ a ⬝ᵥ x) :
    ∀ x ∈ N1plus K, 0 ≤ a ⬝ᵥ x := by sorry

end LovaszSchrijver.NPlus

