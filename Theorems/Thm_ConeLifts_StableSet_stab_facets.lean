import Mathlib
import Definitions.Def_ConeLifts_StableSet_stab
import Definitions.Def_ConeLifts_StableSet_IsFacet

namespace ConeLifts.StableSet

/-- **Theorem 5.2, proof** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 19): for every graph
`G` on `{1, …, n}` with `n ≥ 1`, the `n` nonnegativities `xᵢ ≥ 0` give facets
`{x ∈ STAB(G) : xᵢ = 0}` of `STAB(G)`, and `STAB(G)` has some facet that does not touch the
origin — the two ingredients of the set of facets `F′` of the proof. The hypothesis `n ≥ 1` is
the paper's reading of "a graph with n vertices" (for `n = 0`, `STAB(G)` is a point and has no
facet). -/
theorem stab_facets {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    (∀ i : Fin n, IsFacet (stab G) {x | x ∈ stab G ∧ x i = 0}) ∧
      ∃ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet (stab G) F ∧
        (0 : EuclideanSpace ℝ (Fin n)) ∉ F := by sorry

end ConeLifts.StableSet

