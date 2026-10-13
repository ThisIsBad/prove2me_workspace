import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_Poset

namespace SingleMachinePrec.Framework

/-- An instance of `1|prec|∑ w_j C_j` (p. 653): a set `N` of jobs (finite wherever it is used),
a partial order `P` on `N` (reflexive, antisymmetric, transitive) giving the precedence
constraints, and nonnegative processing times `p_j` and weights `w_j`. -/
structure Instance (N : Type*) where
  /-- The precedence constraints: `P i j` with `i ≠ j` means job `i` must finish before `j`. -/
  P : N → N → Prop
  isPartialOrder : IsPartialOrder N P
  /-- Processing times. -/
  p : N → ℝ
  /-- Weights. -/
  w : N → ℝ
  p_nonneg : ∀ j, 0 ≤ p j
  w_nonneg : ∀ j, 0 ≤ w j

variable {N : Type*}

/-- The adjacency rule of the vertex cover graph `G^S_P` as printed on p. 656: nodes `(i, j)`
and `(k, ℓ)` are adjacent if `j = k` and `i = ℓ`, or `j = k` and `(i, ℓ) ∈ P`, or
`(i, ℓ) ∈ P` and `(k, j) ∈ P`. (The rule is not symmetric as printed; `vertexCoverGraph` takes
its symmetric closure.) -/
def csRule (P : N → N → Prop) (u v : IncPair P) : Prop :=
  (u.1.2 = v.1.1 ∧ u.1.1 = v.1.2) ∨ (u.1.2 = v.1.1 ∧ P u.1.1 v.1.2) ∨
    (P u.1.1 v.1.2 ∧ P v.1.1 u.1.2)

/-- The vertex cover graph `G^S_P` of Correa and Schulz (§2.2, p. 656): one node for each
incomparable pair `(i, j)`, and two distinct nodes are adjacent when the adjacency rule
`csRule` holds in one of the two orders. Its edges are exactly the constraints (1)–(3) of
[CS-IP]. It depends only on the precedence constraints `P`. -/
def vertexCoverGraph (P : N → N → Prop) : SimpleGraph (IncPair P) where
  Adj u v := u ≠ v ∧ (csRule P u v ∨ csRule P v u)
  symm := ⟨fun _u _v h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _u h => h.1 rfl⟩

/-- The weight `w_{(i,j)} = p_i · w_j` of the node `(i, j)` of `G^S_P` (p. 656): the processing
time of the *first* job times the weight of the *second*. -/
def vertexWeight (S : Instance N) (u : IncPair S.P) : ℝ :=
  S.p u.1.1 * S.w u.1.2

/-- The weight `w(C) = ∑_{u ∈ C} w_u` of a finite set of nodes of `G^S_P`. -/
def weight (S : Instance N) (C : Finset (IncPair S.P)) : ℝ :=
  ∑ u ∈ C, vertexWeight S u

open Classical in
/-- `OPT`: the minimum weight of a vertex cover of `G^S_P` (the minimum is over the finitely many
vertex covers, a family that contains the set of all nodes). -/
noncomputable def OPT [Fintype N] (S : Instance N) : ℝ :=
  (Finset.univ.filter
      (fun C : Finset (IncPair S.P) => (vertexCoverGraph S.P).IsVertexCover (C : Set _))).inf'
    ⟨Finset.univ, by simp [SimpleGraph.isVertexCover_univ]⟩ (weight S)

end SingleMachinePrec.Framework
