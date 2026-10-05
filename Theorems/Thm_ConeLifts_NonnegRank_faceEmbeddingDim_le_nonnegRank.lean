import Mathlib
import Definitions.Def_ConeLifts_NonnegRank_IsPolytope
import Definitions.Def_ConeLifts_NonnegRank_Face
import Definitions.Def_ConeLifts_NonnegRank_nonnegRank

namespace ConeLifts.NonnegRank

/-- **Corollary 4.12** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 15). Let `C ⊆ ℝⁿ` be a
polytope (with the origin in its interior) and `k` the smallest integer such that there is an
embedding of the face lattice `L(C)` into the Boolean lattice `2^[k]`. Then `rank₊(C) ≥ k`.

The set of such `k` is nonempty for a polytope (a polytope has finitely many faces, and
`F ↦ {faces contained in F}` embeds `L(C)` into `2^[#L(C)]`), so the `sInf` is its minimum.
"Embedding" is an order embedding, as in Theorem 4.11. `rank₊(C)` is valued in `ℕ∞`. -/
theorem faceEmbeddingDim_le_nonnegRank {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) :
    ((sInf {k : ℕ | Nonempty (Face C ↪o Finset (Fin k))} : ℕ) : ℕ∞) ≤ nonnegRank C := by sorry

end ConeLifts.NonnegRank

