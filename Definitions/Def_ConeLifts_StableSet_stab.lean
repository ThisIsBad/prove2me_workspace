import Mathlib

namespace ConeLifts.StableSet

/-- The **incidence vector** `χ_S ∈ {0, 1}ⁿ` of a vertex set `S ⊆ V = {1, …, n}` (Gouveia,
Parrilo & Thomas, arXiv:1111.3164v2, §5.1, p. 18): `(χ_S)_i = 1` if `i ∈ S` and `(χ_S)_i = 0`
otherwise. The vertices are indexed by `Fin n` (vertex `i + 1` of the paper is `i : Fin n`), and
the vector lives in `ℝⁿ = EuclideanSpace ℝ (Fin n)`. -/
noncomputable def incidenceVector {n : ℕ} (S : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if i ∈ S then (1 : ℝ) else 0)

/-- The **stable set polytope** of a graph `G` on the vertex set `V = {1, …, n}` (Gouveia,
Parrilo & Thomas, arXiv:1111.3164v2, §5.1, p. 18):
`STAB(G) = conv{χ_S : S is a stable set of G}`, where `S ⊆ V` is stable if there are no edges
between elements of `S` (Mathlib's `SimpleGraph.IsIndepSet`). -/
def stab {n : ℕ} (G : SimpleGraph (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  convexHull ℝ
    {x | ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ x = incidenceVector S}

end ConeLifts.StableSet
