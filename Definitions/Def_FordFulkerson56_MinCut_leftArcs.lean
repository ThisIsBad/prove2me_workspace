import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow

namespace FordFulkerson56.MinCut

variable {V E : Type*} [Fintype E] [DecidableEq E]

/-- The set `S` of the proof of Theorem 1 (p. 400): the arcs saturated in every maximal flow. -/
noncomputable def saturatedSet (N : Network V E) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => ∀ f, IsMaxFlow N f → Saturated N f e)

/-- `IsLeftVertex N e v` (p. 401): `v` is the vertex of `e` that occurs first in a positive chain flow
of some maximal flow, i.e. there are a maximal flow `f` and an arrangement `(p, vs)` of a chain from
the source to the sink with `0 < f p.toFinset`, in which `e` is the `i`-th arc and `v` the `i`-th
vertex (the vertex from which the walk enters `e`). -/
def IsLeftVertex (N : Network V E) (e : E) (v : V) : Prop :=
  ∃ f, IsMaxFlow N f ∧ ∃ (p : List E) (vs : List V),
    IsChainWalk N N.source N.sink p vs ∧ 0 < f p.toFinset ∧
    ∃ i : ℕ, p[i]? = some e ∧ vs[i]? = some v

/-- The set `L` of left arcs of `S` (p. 401): the arcs `e ∈ S` with a left vertex `v` for which there
are a maximal flow `f` and a chain (possibly null) joining the source and `v` none of whose arcs is
saturated by `f`. -/
noncomputable def leftArcs (N : Network V E) : Finset E := by
  classical
  exact (saturatedSet N).filter (fun e => ∃ v, IsLeftVertex N e v ∧
    ∃ f, IsMaxFlow N f ∧ ∃ C, IsChain N N.source v C ∧ ∀ e' ∈ C, ¬ Saturated N f e')

end FordFulkerson56.MinCut
