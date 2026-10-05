import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain

namespace BergeMatching.Core

/-- Adjacency of the graph `Ḡ` (p. 842) on `Option V`, where `none` is the added vertex `ā`:
two vertices of `G` are adjacent as in `G`, `ā` is adjacent exactly to the neutral points, and
`ā` has no loop. -/
def barAdj {V : Type} (G : SimpleGraph V) (M : G.Subgraph) : Option V → Option V → Prop
  | some u, some v => G.Adj u v
  | none, some n => IsNeutral M n
  | some n, none => IsNeutral M n
  | none, none => False

/-- The graph `Ḡ` (p. 842): `G` together with a new vertex `ā = none` joined to every neutral
point. -/
def barGraph {V : Type} (G : SimpleGraph V) (M : G.Subgraph) : SimpleGraph (Option V) where
  Adj := barAdj G M
  symm := ⟨fun a b h => by
    cases a <;> cases b <;> simp_all [barAdj, G.adj_comm]⟩
  loopless := ⟨fun a h => by
    cases a <;> simp_all [barAdj]⟩

/-- The strong edges of `Ḡ` (p. 842): the edges of the matching `M`, and the edges joining `ā`
to the neutral points. Every other edge of `Ḡ` is weak. -/
def barStrong {V : Type} {G : SimpleGraph V} (M : G.Subgraph) : Set (Sym2 (Option V)) :=
  Sym2.map some '' M.edgeSet ∪ {e | ∃ n, IsNeutral M n ∧ e = s(none, some n)}

/-- The arrow on the edge `(z, x)` of `Ḡ`, directed from `z` to `x` (p. 842): there is an
alternating chain of `Ḡ` (with respect to `barStrong M`) from `ā` to `x` with at least one edge,
whose last edge is `(z, x)`. -/
def Arrow {V : Type} (G : SimpleGraph V) (M : G.Subgraph) (z x : Option V) : Prop :=
  ∃ p : (barGraph G M).Walk none x,
    IsAlternatingWrt (barStrong M) p ∧ p.length ≠ 0 ∧ p.penultimate = z

/-- "`ā` is inaccessible" (pp. 842–843), read as: no arrow is directed to `ā`. -/
def AbarInaccessible {V : Type} (G : SimpleGraph V) (M : G.Subgraph) : Prop :=
  ∀ z : Option V, ¬ Arrow G M z none

/-- An *inaccessible* point (p. 842): a non-neutral vertex `x` not adjacent to a directed edge,
i.e. no edge at `x` carries an arrow in either direction. The set of these is `I`. -/
def IsInaccessible {V : Type} (G : SimpleGraph V) (M : G.Subgraph) (x : V) : Prop :=
  ¬ IsNeutral M x ∧ ∀ y : Option V, ¬ Arrow G M y (some x) ∧ ¬ Arrow G M (some x) y

/-- A *weak* point (p. 842): a non-neutral vertex `x` adjacent to a weak edge directed to `x`
and not to a strong edge directed to `x`. The set of these is `W`. -/
def IsWeakPt {V : Type} (G : SimpleGraph V) (M : G.Subgraph) (x : V) : Prop :=
  ¬ IsNeutral M x ∧
    (∃ z, Arrow G M z (some x) ∧ s(z, some x) ∉ barStrong M) ∧
    ¬ ∃ z, Arrow G M z (some x) ∧ s(z, some x) ∈ barStrong M

/-- A *strong* point (pp. 842–843): a non-neutral vertex `x` adjacent to a strong edge directed
to `x` and not to a weak edge directed to `x`. The set of these is `S`. -/
def IsStrongPt {V : Type} (G : SimpleGraph V) (M : G.Subgraph) (x : V) : Prop :=
  ¬ IsNeutral M x ∧
    (∃ z, Arrow G M z (some x) ∧ s(z, some x) ∈ barStrong M) ∧
    ¬ ∃ z, Arrow G M z (some x) ∧ s(z, some x) ∉ barStrong M

/-- A *medium* point (p. 843): a non-neutral vertex `x` adjacent to a strong edge directed to `x`
and to a weak edge directed to `x`. The paper calls the set of these `M`; here `M` is the
matching, so the class is `IsMedium`. -/
def IsMedium {V : Type} (G : SimpleGraph V) (M : G.Subgraph) (x : V) : Prop :=
  ¬ IsNeutral M x ∧
    (∃ z, Arrow G M z (some x) ∧ s(z, some x) ∈ barStrong M) ∧
    (∃ z, Arrow G M z (some x) ∧ s(z, some x) ∉ barStrong M)

end BergeMatching.Core
