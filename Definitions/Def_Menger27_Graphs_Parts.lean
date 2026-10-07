import Mathlib
import Definitions.Def_Menger27_Graphs_Separation

namespace Menger27.Graphs

/-- `IrreduciblyNPointConnected K P Q n` (Menger 1927, p. 101, "irreduzibel n-punktig
zusammenhängend"): `K` is `n`-point connected between `P` and `Q`, and no proper part of `K`
(a spanning subgraph `H < K`, i.e. `K` with at least one edge removed) is. -/
def IrreduciblyNPointConnected {V : Type*} (K : SimpleGraph V) (P Q : Finset V) (n : ℕ) :
    Prop :=
  NPointConnected K P Q n ∧ ∀ H : SimpleGraph V, H < K → ¬ NPointConnected H P Q n

/-- `sideVerts G P S` (Menger 1927, p. 102): the vertices that can be reached in `G` from a vertex
of `P − S` by a walk that never meets `S`; these are the vertices of the components of `G − S`
that meet `P − S·P`. -/
def sideVerts {V : Type*} (G : SimpleGraph V) (P S : Finset V) : Set V :=
  {v | ∃ x ∈ P, ∃ w : G.Walk x v, ∀ u ∈ w.support, u ∉ S}

/-- `sidePart G P S` (Menger 1927, p. 102, the part `K₁` together with its end points in
`S − S·P`): the spanning subgraph of `G` whose edges are the edges `uv` of `G` with at least one
end in `sideVerts G P S` and each end in `sideVerts G P S` or in `S − P`. -/
def sidePart {V : Type*} (G : SimpleGraph V) (P S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (u ∈ sideVerts G P S ∨ v ∈ sideVerts G P S) ∧
    (u ∈ sideVerts G P S ∨ (u ∈ S ∧ u ∉ P)) ∧ (v ∈ sideVerts G P S ∨ (v ∈ S ∧ v ∉ P))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.1.symm, h.2.2.2, h.2.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

end Menger27.Graphs
