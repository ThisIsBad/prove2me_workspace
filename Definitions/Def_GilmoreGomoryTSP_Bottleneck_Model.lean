import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.Bottleneck

open MeasureTheory

/-- The bottleneck objective, p. 670: `m(ψ) = max_i c_{i ψ(i)}`, a maximum over the nonempty
finite set of jobs. -/
noncomputable def m {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => GilmoreGomoryTSP.MinCost.c f g A B i (ψ i))

/-- The interchange `α_{ij}` applied to `ψ`, (5)–(7), p. 658: `ψ α_{ij}`, first apply `α_{ij}`,
then `ψ`. -/
def interchange {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  ψ * Equiv.swap i j

/-- The graph `G_ψ`, p. 660: an undirected arc linking `i` and `ψ(i)` for every `i`
(loops `ψ(i) = i` are dropped; they do not affect connectivity). -/
def graphOf {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1))) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun i j => ψ i = j)

/-- The arcs `R_{q,q+1}` for `q ∈ T`; the arc indexed by `q : Fin n` joins `q.castSucc` and
`q.succ` (the paper's nodes `q` and `q + 1`). -/
def adjArcs {n : ℕ} (T : Finset (Fin n)) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun i j => ∃ q ∈ T, i = q.castSucc ∧ j = q.succ)

/-- `G_φ ∪ {R_{q,q+1} : q ∈ T}` is connected. -/
def Connects {n : ℕ} (φ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) : Prop :=
  (graphOf φ ⊔ adjArcs T).Connected

/-- A spanning tree of `G_φ` made of arcs `R_{q,q+1}`, pp. 660 and 662: a set of such arcs that
connects `G_φ`, no proper subset of which connects it. -/
def IsAdjSpanningTree {n : ℕ} (φ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) : Prop :=
  Connects φ T ∧ ∀ T' ⊂ T, ¬ Connects φ T'

/-- The bottleneck arc cost, p. 670: the arc `R_{q,q+1}` has cost `c_{q φ(q+1)}`. -/
noncomputable def arcCost {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (φ : Equiv.Perm (Fin (n + 1))) (q : Fin n) : ℝ :=
  GilmoreGomoryTSP.MinCost.c f g A B q.castSucc (φ q.succ)

/-- A minimum spanning tree of `G_φ` with the costs `c_{q φ(q+1)}`, p. 670: an adjacent-arc
spanning tree whose total cost is at most that of every adjacent-arc spanning tree. -/
def IsMinSpanningTree {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (φ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) : Prop :=
  IsAdjSpanningTree φ T ∧
    ∀ T', IsAdjSpanningTree φ T' → ∑ q ∈ T, arcCost f g A B φ q ≤ ∑ q ∈ T', arcCost f g A B φ q

/-- The tour `ψ′ = φ α_{j_1 j_1+1} ⋯ α_{j_m j_m+1}`, p. 670, with `j_1 < ⋯ < j_m` the arcs of `T`
in increasing order: the interchanges are applied to `φ` one after another, lowest index first. -/
def psiPrime {n : ℕ} (φ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  ((List.finRange n).filter (fun q => q ∈ T)).foldl
    (fun ψ q => interchange ψ q.castSucc q.succ) φ

/-- Condition (22a), p. 666: `i ≤ q < φ⁻¹ψ(i)`. -/
def Cond22a {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) (i : Fin (n + 1)) : Prop :=
  (i : ℕ) ≤ q ∧ (q : ℕ) < (φ.symm (ψ i) : ℕ)

/-- Condition (22b), p. 666: `φ⁻¹ψ(j) ≤ q < j`. -/
def Cond22b {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) (j : Fin (n + 1)) : Prop :=
  (φ.symm (ψ j) : ℕ) ≤ q ∧ (q : ℕ) < j

/-- The arcs `R_{q,q+1}` added to `G_φ` to form `G_ψ*`, p. 668: those `q` for which (22a) holds
for some `i` or (22b) holds for some `j`. -/
noncomputable def starArcs {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun q => (∃ i, Cond22a φ ψ q i) ∨ ∃ j, Cond22b φ ψ q j)

/-- The graph `G_ψ*`, p. 668: all arcs `R_{q φ(q)}` of `G_φ` and the arcs `R_{q,q+1}` of
`starArcs φ ψ`. -/
noncomputable def Gstar {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) : SimpleGraph (Fin (n + 1)) :=
  graphOf φ ⊔ adjArcs (starArcs φ ψ)

/-- The undirected graph `G′_φ` of Theorem 6, p. 671, for a directed graph given by its
out-neighbourhoods `Γ i`: an arc `R_{q φ(q)}` iff `φ(q) ∈ Γ_q`, and an arc `R_{q,q+1}` iff
`φ(q+1) ∈ Γ_q`. -/
def Gprime {n : ℕ} (Γ : Fin (n + 1) → Finset (Fin (n + 1))) (φ : Equiv.Perm (Fin (n + 1))) :
    SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun i j =>
    (j = φ i ∧ φ i ∈ Γ i) ∨ ∃ q : Fin n, i = q.castSucc ∧ j = q.succ ∧ φ q.succ ∈ Γ q.castSucc)

end GilmoreGomoryTSP.Bottleneck
