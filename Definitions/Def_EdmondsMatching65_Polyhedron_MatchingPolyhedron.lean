import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace EdmondsMatching65.Polyhedron

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The left side of inequality (2) at node `v` (§2, p. 126): the sum of `x e` over the edges `e`
of `G` which meet `v`. -/
def degSum (G : Graph V E) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => v ∈ G.ends e), x e

/-- The left side of inequality (3) for a node set `S` (§2, p. 126): the sum of `x e` over the
edges `e` of `G` with both ends in `S`. -/
def insideSum (G : Graph V E) (x : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => G.ends e ∈ S.sym2), x e

/-- The polyhedron `C` (§2, pp. 125–126): the vectors `x`, one real coordinate per edge, with
(1) `x e ≥ 0` for every edge;
(2) `∑_{e meets v} x e ≤ 1` for every node `v`;
(3) `∑_{e ⊆ S} x e ≤ r` for every set `S` of `2r + 1` nodes, `r` a strictly positive integer. -/
def matchingPolyhedron (G : Graph V E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v : V, degSum G x v ≤ 1) ∧
    ∀ (S : Finset V) (r : ℕ), 1 ≤ r → S.card = 2 * r + 1 → insideSum G x S ≤ (r : ℝ)}

/-- The set `P` of matching vectors (§2, p. 126): the vectors satisfying condition (I) (every
component is zero or one) and inequality (2). -/
def matchingVectors (G : Graph V E) : Set (E → ℝ) :=
  {x | (∀ e, x e = 0 ∨ x e = 1) ∧ ∀ v : V, degSum G x v ≤ 1}

/-- The linear form (4) (§2, p. 126): `W = ∑_e c e * x e`. -/
def W (c x : E → ℝ) : ℝ :=
  ∑ e, c e * x e

end EdmondsMatching65.Polyhedron
