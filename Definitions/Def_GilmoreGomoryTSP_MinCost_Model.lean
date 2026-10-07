import Mathlib

namespace GilmoreGomoryTSP.MinCost

open MeasureTheory

variable {n : ℕ}

/-- The changeover cost (1) of having job `j` follow job `i`: with `N = n + 1` jobs indexed by
`Fin (n + 1)`, job `i` starts in state `A i` and ends in state `B i`;
`c_ij = ∫_{B_i}^{A_j} f` if `A_j ≥ B_i` and `c_ij = ∫_{A_j}^{B_i} g` if `B_i > A_j`. -/
noncomputable def c (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) : ℝ :=
  if B i ≤ A j then ∫ x in B i..A j, f x else ∫ x in A j..B i, g x

/-- The total changeover cost (3) of a permutation `ψ`, where `ψ i` is the job following job `i`:
`c(ψ) = ∑_i c_{i ψ(i)}`. -/
noncomputable def cost (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) : ℝ :=
  ∑ i, c f g A B i (ψ i)

/-- Condition (4): `ψ` is a tour if `ψ(s) ≠ s` for every nonempty proper subset `s` of the jobs. -/
def IsTour (ψ : Equiv.Perm (Fin (n + 1))) : Prop :=
  ∀ s : Finset (Fin (n + 1)), s.Nonempty → s ≠ Finset.univ → s.map ψ.toEmbedding ≠ s

/-- `φ` ranks the `A`: `j > i` implies `A_{φ(j)} ≥ A_{φ(i)}` (Theorem 1, step P3). -/
def RanksA (A : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) : Prop :=
  Monotone (A ∘ φ)

/-- The interchange `α_ij` (5): it exchanges `i` and `j` and fixes every other job. Applying it to
`ψ` gives `ψ α_ij` (6), "first apply `α_ij`, then `ψ`", i.e. the product `ψ * alpha i j`. -/
def alpha (i j : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap i j

/-- The cost of applying the interchange `α_ij` to `ψ`: `c_ψ(α_ij) = c(ψ α_ij) − c(ψ)` (p. 658). -/
noncomputable def interchangeCost (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) : ℝ :=
  cost f g A B (ψ * alpha i j) - cost f g A B ψ

/-- The graph `G_ψ` (p. 660): `N` nodes and an undirected arc linking the `i`th and `ψ(i)`th
nodes (loops `ψ(i) = i` are omitted, which does not affect connectivity). -/
def graph (ψ : Equiv.Perm (Fin (n + 1))) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel fun i j => ψ i = j

/-- `G_ψ` together with the additional undirected arcs `R_ij`, `(i, j) ∈ E`. -/
def graphWith (ψ : Equiv.Perm (Fin (n + 1))) (E : Finset (Fin (n + 1) × Fin (n + 1))) :
    SimpleGraph (Fin (n + 1)) :=
  graph ψ ⊔ SimpleGraph.fromRel fun i j => (i, j) ∈ E

/-- A spanning tree of `G_ψ` (p. 660): "a minimal set of additional arcs that connect a graph
`G_ψ`", minimal under inclusion: `G_ψ ∪ E` is connected and no proper subset of `E` connects. -/
def IsSpanningTree (ψ : Equiv.Perm (Fin (n + 1))) (E : Finset (Fin (n + 1) × Fin (n + 1))) :
    Prop :=
  (graphWith ψ E).Connected ∧ ∀ E' ⊂ E, ¬ (graphWith ψ E').Connected

/-- The cost of a set of arcs `E` relative to `ψ`: `c_ψ(τ) = ∑ {c_ψ(α_ij) | R_ij ∈ τ}` (p. 662). -/
noncomputable def arcSetCost (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (E : Finset (Fin (n + 1) × Fin (n + 1))) : ℝ :=
  ∑ e ∈ E, interchangeCost f g A B ψ e.1 e.2

/-- The adjacent arc `R_{q,q+1}`, indexed by `q : Fin n`: it joins the jobs `q.castSucc` and
`q.succ` (the paper's jobs `q` and `q + 1`, 1-based). -/
def adjArc (q : Fin n) : Fin (n + 1) × Fin (n + 1) :=
  (q.castSucc, q.succ)

/-- The set of arcs `{R_{q,q+1} | q ∈ T}`. -/
def adjArcs (T : Finset (Fin n)) : Finset (Fin (n + 1) × Fin (n + 1)) :=
  T.image adjArc

/-- `T` is a spanning tree of `G_ψ` consisting only of adjacent arcs `R_{q,q+1}`. -/
def IsAdjTree (ψ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) : Prop :=
  IsSpanningTree ψ (adjArcs T)

/-- The cost `c_ψ(T) = ∑_{q ∈ T} c_ψ(α_{q,q+1})` of a set of adjacent arcs. -/
noncomputable def adjTreeCost (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) : ℝ :=
  ∑ q ∈ T, interchangeCost f g A B ψ q.castSucc q.succ

/-- `T` is a minimal cost spanning tree of `G_ψ` among the spanning trees made of adjacent arcs
(what steps S1–S3 compute; by Lemma 2 its cost is also minimal among all spanning trees). -/
def IsMinCostAdjTree (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) : Prop :=
  IsAdjTree ψ T ∧ ∀ T' : Finset (Fin n), IsAdjTree ψ T' →
    adjTreeCost f g A B ψ T ≤ adjTreeCost f g A B ψ T'

/-- Node `i` is of type 1 relative to `ψ` if `B_i ≤ A_{ψ(i)}`, otherwise of type 2 (p. 663). -/
def IsType1 (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) : Prop :=
  B i ≤ A (ψ i)

/-- Execute the adjacent interchanges `α_{q,q+1}` listed in `l` on `ψ`, first to last:
`ψ α_{l_1,l_1+1} α_{l_2,l_2+1} ⋯`. -/
def applyAdj (ψ : Equiv.Perm (Fin (n + 1))) (l : List (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  l.foldl (fun σ q => σ * alpha q.castSucc q.succ) ψ

/-- The execution order of Lemma 5 (p. 664) and steps T2–T4 (p. 673) for a set `T` of adjacent
arcs: first the type 1 interchanges (lower node of type 1 relative to `φ`) in decreasing order of
index, then the type 2 interchanges in increasing order of index. The filter conditions are
`IsType1 A B φ q.castSucc` and its negation, written out. -/
noncomputable def execOrder (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1)))
    (T : Finset (Fin n)) : List (Fin n) :=
  ((T.filter fun q => B q.castSucc ≤ A (φ q.castSucc)).sort (· ≤ ·)).reverse ++
    (T.filter fun q => ¬ B q.castSucc ≤ A (φ q.castSucc)).sort (· ≤ ·)

/-- The tour `ψ* = φ α_{i_1,i_1+1} ⋯ α_{i_l,i_l+1} α_{j_1,j_1+1} ⋯ α_{j_m,j_m+1}` (T4, p. 673):
the interchanges of `T` executed on `φ` in the order `execOrder`. -/
noncomputable def psiStar (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1)))
    (T : Finset (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  applyAdj φ (execOrder A B φ T)

end GilmoreGomoryTSP.MinCost
