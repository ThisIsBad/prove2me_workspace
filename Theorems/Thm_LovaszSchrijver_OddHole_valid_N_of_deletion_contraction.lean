import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones
import Definitions.Def_LovaszSchrijver_OddHole_DeletionContraction

namespace LovaszSchrijver.OddHole

/-- Lemma 2.2 (p. 178), cone form: let `K ⊆ FR(G)` be a closed convex cone. If for some
node `v` both the deletion and the contraction of `v` give inequalities valid for `K`
(read on the slice `x₀ = 1`), then `aᵀx ≤ b` is valid for `N(K)` (read on `x₀ = 1`). -/
theorem valid_N_of_deletion_contraction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (K : Set (Option V → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKFR : K ⊆ FR G)
    (a : V → ℝ) (b : ℝ) (v : V)
    (hdel : Valid {x | hom x ∈ K} (deletion a v) b)
    (hcon : Valid {x | hom x ∈ K} (contraction G a v) (b - a v)) :
    Valid {x | hom x ∈ N K} a b := by sorry

end LovaszSchrijver.OddHole

