import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic

namespace PathsTreesFlowers.Duality

open EdmondsMatching65.Polyhedron (IsMatching)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- An edge of `G` *inside a part* of the partition `P`: both of its end-points lie in one part.
These are the edges that disappear when every part of `P` is shrunk to a single vertex. -/
def InsidePart (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P : Finpartition (Finset.univ : Finset V)) (e : E) : Prop :=
  ∃ U ∈ P.parts, G.ends e ∈ U.sym2

instance (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P : Finpartition (Finset.univ : Finset V)) : DecidablePred (InsidePart G P) := fun e => by
  unfold InsidePart; infer_instance

/-- The vertex of the shrunken graph to which the vertex `v` of `G` is sent: the part of `P`
containing `v`. -/
def toPart (P : Finpartition (Finset.univ : Finset V)) (v : V) : {U : Finset V // U ∈ P.parts} :=
  ⟨P.part v, P.part_mem.2 (Finset.mem_univ v)⟩

/-- 4.9–4.11, pp. 456–457: *shrinking* every part of the partition `P` of the vertices of `G`.
The vertices of `G/P` are the parts of `P` (a part `U` is the vertex `U/U`); the edges of `G/P`
are the edges of `G` that do not have both end-points in one part, each keeping its identity, with
each end-point replaced by the part containing it. Edges with both end-points in one part
disappear. Shrinking a single set `U` is the case where `U` is the only part with more than one
vertex (`blockPartition`). -/
def shrink (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P : Finpartition (Finset.univ : Finset V)) :
    EdmondsMatching65.Polyhedron.Graph {U : Finset V // U ∈ P.parts} {e : E // ¬ InsidePart G P e}
    where
  ends e := Sym2.map (toPart P) (G.ends e.1)
  loopless e := by
    intro hdiag
    apply e.2
    induction h : G.ends e.1 using Sym2.ind with
    | h a b =>
      rw [h, Sym2.map_mk, Sym2.mk_isDiag_iff] at hdiag
      refine ⟨P.part a, P.part_mem.2 (Finset.mem_univ a), ?_⟩
      rw [h, Finset.mk_mem_sym2_iff]
      refine ⟨P.mem_part (Finset.mem_univ a), ?_⟩
      have : P.part a = P.part b := congrArg Subtype.val hdiag
      rw [this]
      exact P.mem_part (Finset.mem_univ b)

/-- 4.10, p. 457: `M/P = M ∩ (G/P)`, the edges of `M` that survive the shrinking. -/
def shrinkMatching (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P : Finpartition (Finset.univ : Finset V)) (M : Finset E) :
    Finset {e : E // ¬ InsidePart G P e} :=
  M.subtype _

/-- The relation "`u = v`, or both lie in `U`". -/
def blockSetoid (U : Finset V) : Setoid V where
  r u v := u = v ∨ (u ∈ U ∧ v ∈ U)
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
    · rintro u v (h | h)
      · exact Or.inl h.symm
      · exact Or.inr ⟨h.2, h.1⟩
    · rintro u v w (rfl | h) (rfl | h')
      · exact Or.inl rfl
      · exact Or.inr h'
      · exact Or.inr h
      · exact Or.inr ⟨h.1, h'.2⟩

instance (U : Finset V) : DecidableRel (blockSetoid U).r := fun u v =>
  show Decidable (u = v ∨ (u ∈ U ∧ v ∈ U)) from inferInstance

/-- The partition of the vertices of `G` whose parts are `U` (if non-empty) and the singletons of
the vertices outside `U`. Shrinking along it is shrinking the single set `U` (4.9): `G/U`. -/
def blockPartition (U : Finset V) : Finpartition (Finset.univ : Finset V) :=
  Finpartition.ofSetoid (blockSetoid U)

/-- 4.10–4.11, pp. 457–458: the *blossom sets* of `(G, M)`, i.e. the vertex sets of `G` absorbed
into one vertex by successively shrinking blossoms (the complete expansion of a pseudovertex,
together with the single vertices of `G`). A single vertex is a blossom set. If `U₀, …, U_{2k}`
(`k ≥ 1`) are pairwise disjoint blossom sets and `e₀, …, e_{2k}` are edges of `G` such that `eᵢ`
joins a vertex of `Uᵢ` to a vertex of `U_{(i+1) mod (2k+1)}` and `eᵢ ∈ M` exactly when `i` is odd,
then — the `Uᵢ` having been shrunk — the `eᵢ` form a blossom `B` with base `U₀` for the current
matching, and shrinking `B` absorbs `U₀ ∪ … ∪ U_{2k}` into one pseudovertex. -/
inductive IsBlossomSet (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) :
    Finset V → Prop
  | single (v : V) : IsBlossomSet G M {v}
  | circuit (k : ℕ) (U : ℕ → Finset V) (e : ℕ → E) (hk : 1 ≤ k)
      (hU : ∀ i < 2 * k + 1, IsBlossomSet G M (U i))
      (hdisj : ∀ i < 2 * k + 1, ∀ j < 2 * k + 1, i ≠ j → Disjoint (U i) (U j))
      (he : ∀ i < 2 * k + 1, ∃ a ∈ U i, ∃ b ∈ U ((i + 1) % (2 * k + 1)), G.ends (e i) = s(a, b))
      (hM : ∀ i < 2 * k + 1, (e i ∈ M ↔ Odd i)) :
      IsBlossomSet G M ((Finset.range (2 * k + 1)).biUnion U)

end PathsTreesFlowers.Duality
