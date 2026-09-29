import Mathlib
import Definitions.Def_ChvatalPolytopes_Neighbors_StablePolytope
import Definitions.Def_ChvatalPolytopes_Neighbors_IsBicoloration

namespace ChvatalPolytopes.Neighbors

/-- **The certificate of the "if" part of Theorem 6.2** (Chvátal 1975, p. 149, proof of
Theorem 6.2, (i)). Let `Y, Z` be stable sets of `G` with incidence vectors `y, z`, and let
`D = (Y − Z) ∪ (Z − Y)`. Suppose the subgraph `H` of `G` induced by `D` is connected, and let
`T` be a spanning tree of `H`. Let `c'_u` (`u ∈ D`) and `m` be as specified by Lemma 6.1 for `T`
with the bicoloration `D = (Y − Z) ∪ (Z − Y)`. Let `c_u = c'_u` for `u ∈ D`, `c_u = 1` if
`u ∈ Y ∩ Z` and `c_u = −1` if `u ∉ Y ∪ Z`. Then `Σ (c_u x_u : u ∈ V) ≤ m + |Y ∩ Z|` for all
`x ∈ S(G)`, with equality if and only if `x = y` or `x = z`. -/
theorem symmDiff_tree_certificate {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Y Z : Finset V)
    (hY : G.IsIndepSet (Y : Set V)) (hZ : G.IsIndepSet (Z : Set V))
    (hH : (G.induce (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V)).Connected)
    (T : SimpleGraph (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V))
    (hTsub : T ≤ G.induce (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V)) (hT : T.IsTree)
    (c' : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) → ℕ) (m : ℕ)
    (hc' : ∀ x ∈ stableVectors T,
      (∑ u, (c' u : ℝ) * x u ≤ (m : ℝ)) ∧
      (∑ u, (c' u : ℝ) * x u = (m : ℝ) ↔
        x = incidenceVector (Finset.univ.filter fun u : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) => u.1 ∈ Y \ Z) ∨
        x = incidenceVector (Finset.univ.filter fun u : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) => u.1 ∈ Z \ Y))) :
    let c : V → ℤ := fun u =>
      if h : u ∈ (Y \ Z) ∪ (Z \ Y) then (c' ⟨u, by simpa using h⟩ : ℤ)
      else if u ∈ Y ∩ Z then 1 else -1
    ∀ x ∈ stableVectors G,
      (∑ u, (c u : ℝ) * x u ≤ (m : ℝ) + ((Y ∩ Z).card : ℝ)) ∧
      (∑ u, (c u : ℝ) * x u = (m : ℝ) + ((Y ∩ Z).card : ℝ) ↔
        x = incidenceVector Y ∨ x = incidenceVector Z) := by sorry

end ChvatalPolytopes.Neighbors

