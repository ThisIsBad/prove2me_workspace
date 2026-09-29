import Mathlib

namespace ChvatalPolytopes.Perfect

/-- The incidence vector `(x_u : u ∈ V)` of a finite vertex set `s`: `x_u = 1` if `u ∈ s`
and `x_u = 0` otherwise. -/
def incidenceVector {V : Type*} [DecidableEq V] (s : Finset V) : V → ℝ :=
  fun u => if u ∈ s then 1 else 0

/-- `S(G)` (Chvátal 1975, p. 139): the set of all zero–one vectors `(x_u : u ∈ V)` such that the
set `{u : x_u = 1}` is stable in `G`, i.e. the incidence vectors of the stable sets of `G`. -/
def stableVectors {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧ x = incidenceVector s}

/-- The stable set polytope `P(G)` (Chvátal 1975, pp. 138–139): the convex hull of `S(G)`
in `ℝ^V`. -/
def stablePolytope {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Set (V → ℝ) :=
  convexHull ℝ (stableVectors G)

/-- `C(G)` (Chvátal 1975, p. 139): the vertex sets `W` of the cliques of `G`, where a *clique* is
a **maximal** complete subgraph; i.e. the finsets `W` that are complete in `G` and are not
properly contained in any complete finset. -/
noncomputable def maximalCliques {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun W : Finset V => Maximal (fun W : Finset V => G.IsClique (W : Set V)) W)

theorem mem_maximalCliques {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) :
    W ∈ maximalCliques G ↔ Maximal (fun W : Finset V => G.IsClique (W : Set V)) W := by
  unfold maximalCliques
  simp

end ChvatalPolytopes.Perfect
