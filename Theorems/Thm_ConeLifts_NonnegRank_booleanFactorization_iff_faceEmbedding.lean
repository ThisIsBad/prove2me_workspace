import Mathlib
import Definitions.Def_ConeLifts_NonnegRank_IsPolytope
import Definitions.Def_ConeLifts_NonnegRank_Face
import Definitions.Def_ConeLifts_NonnegRank_HasBooleanFactorization

namespace ConeLifts.NonnegRank

/-- **Theorem 4.11** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 15). For a polytope `C`
(with the origin in its interior), there is a Boolean factorization of `supp(S_C)` of intermediate
dimension `k` if and only if there is a lattice embedding of the face lattice `L(C)` into the
Boolean lattice `2^[k]` (`Finset (Fin k)` ordered by inclusion).

Reading decision: "lattice embedding" is an order embedding (`H ⊆ F ↔ φ H ⊆ φ F`), which is exactly
what both directions of the paper's proof use and produce; the map `φ(F) = ⋃_{v ∈ F} A(v)` built in
the proof need not preserve joins or meets. -/
theorem booleanFactorization_iff_faceEmbedding {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) (k : ℕ) :
    HasBooleanFactorization C k ↔ Nonempty (Face C ↪o Finset (Fin k)) := by sorry

end ConeLifts.NonnegRank

