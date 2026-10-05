import Mathlib
import Definitions.Def_ConeLifts_NonnegRank_IsPolytope
import Definitions.Def_ConeLifts_NonnegRank_Face
import Definitions.Def_ConeLifts_NonnegRank_nonnegRank

namespace ConeLifts.NonnegRank

/-- **Corollary 4.13** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 16). If `C ⊆ ℝⁿ` is a
polytope (with the origin in its interior), then:

1. (antichain bound) if `p` is the size of an antichain of faces of `C` (no face of the family is
   contained in another), `rank₊(C)` is at least the smallest `k` with `p ≤ (k choose ⌊k/2⌋)`;
   stated for every antichain, which is equivalent to the paper's "largest antichain" because the
   bound is monotone in `p` and a largest antichain is one of them;
2. (Goemans) if `n_C` is the number of faces of `C`, then `rank₊(C) ≥ log₂ n_C`; stated for every
   finite value `k` of `rank₊(C)`, the case `rank₊(C) = +∞` being trivially true.

Faces are exposed faces, including `∅` and `C`; a polytope has finitely many, so `Nat.card` is the
face count. The set `{k | p ≤ (k choose ⌊k/2⌋)}` is nonempty (central binomials are unbounded), so
its `sInf` is its minimum. -/
theorem nonnegRank_face_lattice_bounds {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) :
    (∀ 𝒜 : Finset (Face C), IsAntichain (· ≤ ·) (𝒜 : Set (Face C)) →
        ((sInf {k : ℕ | 𝒜.card ≤ k.choose (k / 2)} : ℕ) : ℕ∞) ≤ nonnegRank C) ∧
    (∀ k : ℕ, (k : ℕ∞) = nonnegRank C → Real.logb 2 (Nat.card (Face C) : ℝ) ≤ k) := by sorry

end ConeLifts.NonnegRank

