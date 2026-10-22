import Definitions.Def_LeightonRao_Uniform_Network

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A nonnegative symmetric edge-distance assignment. Values on nonedges are ignored. -/
def IsDistanceFunction (d : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ d u v) ∧ (∀ u v, d u v = d v u)

/-- Length of a graph walk in the assigned edge distances. -/
noncomputable def walkLen (N : Network V) (d : V → V → ℝ)
    {u v : V} (p : N.graph.Walk u v) : ℝ :=
  (p.darts.map (fun a => d a.fst a.snd)).sum

/-- Shortest path distance on the positive-capacity graph. The walk index is nonempty
under `IsConnectedNet N`; every theorem using it states that assumption. -/
noncomputable def dist (N : Network V) (d : V → V → ℝ) (u v : V) : ℝ :=
  ⨅ p : N.graph.Walk u v, walkLen N d p

/-- Distance `d(T, u)` from a vertex set to a vertex. Meaningful for nonempty `T`; for
`T = ∅` the infimum over the empty index is Lean's junk value `0`. -/
noncomputable def distFrom (N : Network V) (d : V → V → ℝ)
    (T : Finset V) (u : V) : ℝ :=
  ⨅ t : T, dist N d t u

/-- `W = ∑ C(e)d(e)`, counting every undirected edge once. -/
noncomputable def totalWeight (N : Network V) (d : V → V → ℝ) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, N.C u v * d u v

/-- Equation (5): the dual's sum is over unordered vertex pairs. -/
def SatisfiesDistanceConstraint (N : Network V) (d : V → V → ℝ) : Prop :=
  1 ≤ (1 / 2) * ∑ u, ∑ v, dist N d u v

/-- The radius bound is witnessed by walks lying entirely within the component. -/
def HasRadiusLE (N : Network V) (d : V → V → ℝ)
    (S : Finset V) (Δ : ℝ) : Prop :=
  ∃ c ∈ S, ∀ y ∈ S, ∃ p : N.graph.Walk c y,
    (∀ x ∈ p.support, x ∈ S) ∧ walkLen N d p ≤ Δ

/-- Capacity of the edges whose endpoints lie in different partition components. -/
noncomputable def crossCap (N : Network V)
    (P : Finpartition (Finset.univ : Finset V)) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, if P.part u = P.part v then 0 else N.C u v

end LeightonRao.Uniform
