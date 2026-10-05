import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_PriceOfStability_Harmonic_Model
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

section General

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- `cost(F) = Σ_{e ∈ F} c_e` (Claim 4.1, proof, p. 1613, PDF p. 12): the cost of a set of edges
under fixed edge costs. -/
def setCost (c : E → ℝ) (F : Finset E) : ℝ := ∑ e ∈ F, c e

end General

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- Player `i`'s strategies in the undirected fair connection game with a common terminal `s`
(Sect. 2, p. 1607, PDF p. 6, specialised by Sect. 4, p. 1613, PDF p. 12): "a set of edges
`Sᵢ ⊂ E` such that `Sᵢ` connects all nodes in `Tᵢ`", with `Tᵢ = {tᵢ, s}`. Formally, the edge sets
`S ⊆ E(G)` such that `tᵢ` and `s` lie in the same connected component of the graph `(V, S)`.

**Formalization Note.** Edges are unordered pairs `Sym2 V`; strategies are arbitrary connecting edge
sets (not only paths), as in the paper's model. If `tᵢ = s`, the empty set is a strategy. -/
noncomputable def connStrategies (G : SimpleGraph V) (s : V) {ι : Type*} (t : ι → V) (i : ι) :
    Finset (Finset (Sym2 V)) :=
  (Finset.univ : Finset (Sym2 V)).powerset.filter (fun S =>
    (S : Set (Sym2 V)) ⊆ G.edgeSet ∧
      (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).Reachable (t i) s)

/-- The two-player undirected fair connection game of Sect. 4 (p. 1613, PDF p. 12): graph `G`,
fixed edge costs `c`, common terminal `s`, personal terminals `t 0`, `t 1` (the paper's `t₁`, `t₂`),
with Shapley cost sharing. -/
noncomputable def twoPlayerGame (G : SimpleGraph V) (c : Sym2 V → ℝ) (s : V) (t : Fin 2 → V) :
    CongestionGame (Fin 2) (Sym2 V) :=
  PriceOfStability.Harmonic.fairGame (connStrategies G s t) (fun e _ => c e)

/-- An inclusion-minimal strategy of player `i`: a connecting edge set `T` none of whose proper
subsets connects `tᵢ` with `s` (in a graph, a simple `tᵢ`–`s` path, or `∅` when `tᵢ = s`).

**Formalization Note.** The proof of Claim 4.1 (p. 1613, PDF p. 12) treats the strategies of the
reference solution as paths ("following X₁ until X₁ meets with X₂"); this predicate is how that
implicit assumption is stated. -/
def IsMinimalStrategy (G : SimpleGraph V) (s : V) {ι : Type*} (t : ι → V) (i : ι)
    (T : Finset (Sym2 V)) : Prop :=
  T ∈ connStrategies G s t i ∧ ∀ T' ⊂ T, T' ∉ connStrategies G s t i

end Graph

end PriceOfStability.Undirected
