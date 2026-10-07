import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace PathsTreesFlowers.Duality

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- 5.6, p. 462: an *odd set* of vertices: a set with an odd number of vertices, i.e. either one
vertex or `2k + 1` vertices with `k = 1, 2, …`. The empty set is not odd. -/
def IsOddSet (U : Finset V) : Prop :=
  Odd U.card

/-- 5.6, p. 462: the *capacity* of an odd set: one for a set consisting of one vertex, and `k` for
a set of `2k + 1` vertices (`k = 1, 2, …`). -/
def capacity (U : Finset V) : ℕ :=
  if U.card = 1 then 1 else (U.card - 1) / 2

/-- 5.6, p. 462: when the odd set `U` *covers* the edge `e`. A set consisting of one vertex covers
`e` if `e` meets the vertex; a set of `2k + 1` vertices (`k ≥ 1`) covers `e` if both end-points of
`e` are in the set. -/
def Covers (G : EdmondsMatching65.Polyhedron.Graph V E) (U : Finset V) (e : E) : Prop :=
  if U.card = 1 then (∃ v ∈ U, v ∈ G.ends e) else G.ends e ∈ U.sym2

instance (G : EdmondsMatching65.Polyhedron.Graph V E) (U : Finset V) :
    DecidablePred (Covers G U) := fun e => by
  unfold Covers; infer_instance

/-- 5.6, p. 462: an *odd-set cover* of `G`: a family of odd sets of vertices such that each edge
of `G` is covered by a member of the family. -/
def IsOddSetCover (G : EdmondsMatching65.Polyhedron.Graph V E) (S : Finset (Finset V)) : Prop :=
  (∀ U ∈ S, IsOddSet U) ∧ ∀ e : E, ∃ U ∈ S, Covers G U e

/-- The capacity-sum of a family of odd sets. -/
def capacitySum (S : Finset (Finset V)) : ℕ :=
  ∑ U ∈ S, capacity U

/-- An odd-set cover of minimum capacity-sum. -/
def IsMinOddSetCover (G : EdmondsMatching65.Polyhedron.Graph V E) (S : Finset (Finset V)) :
    Prop :=
  IsOddSetCover G S ∧ ∀ T : Finset (Finset V), IsOddSetCover G T → capacitySum S ≤ capacitySum T

end PathsTreesFlowers.Duality
