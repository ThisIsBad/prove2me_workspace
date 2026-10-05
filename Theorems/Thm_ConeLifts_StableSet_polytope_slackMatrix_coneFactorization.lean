import Mathlib
import Definitions.Def_ConeLifts_StableSet_HasConeLift
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_StableSet_IsSlackMatrix
import Definitions.Def_ConeLifts_StableSet_HasConeFactorization

namespace ConeLifts.StableSet

/-- **Theorem 3.3, first sentence** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 9): if a
full-dimensional polytope `P` has a proper `K`-lift then every slack matrix of `P` admits a
`K`-factorization.

`K ⊆ ℝᵐ` is a full-dimensional closed convex cone (Definition 2.1, p. 3). `P ⊆ ℝⁿ` is the convex
hull of a finite set with the origin in its interior (the standing assumption of §3, p. 9, which
also makes `P` full-dimensional), in a space of positive dimension `n ≥ 1`: for `n = 0` the point
`P = {0} = ℝ⁰` has the proper `ℝᵐ`-lift `π = 0`, `L = ℝᵐ`, while `(ℝᵐ)* = {0}` cannot factor its
slack matrix `(1)`. The slack matrices of `P` are encoded by `IsSlackMatrix`: the
canonical slack matrix `(1 - ⟨p, y⟩)` on `ext(P) × ext(P°)` with positively scaled columns. -/
theorem polytope_slackMatrix_coneFactorization {n m : ℕ} (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin m)))
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K, t • x ∈ K)
    (hK_full : (interior K).Nonempty)
    (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP_polytope : ∃ V : Finset (EuclideanSpace ℝ (Fin n)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n))))
    (hP_origin : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior P)
    (hlift : HasProperConeLift K P)
    (M : Matrix (Set.extremePoints ℝ P) (Set.extremePoints ℝ (ConeLifts.Shared.polar P)) ℝ)
    (hM : IsSlackMatrix P M) :
    HasConeFactorization K M := by sorry

end ConeLifts.StableSet

