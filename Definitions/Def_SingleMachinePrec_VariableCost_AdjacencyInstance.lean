import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_VertexCoverGraph

open scoped NNReal

namespace SingleMachinePrec.VariableCost

variable {n : ℕ}

/-- The precedence constraints of the scheduling instance built from a graph `G` on the vertices
`v_1, …, v_n` (proof of Theorem 8.1, p. 664). The jobs are `Fin n ⊕ Fin n`: `Sum.inl i` is the
job `v′_i` and `Sum.inr i` is the job `v″_i` (vertex `v_i` is `i : Fin n`, numbered from `0`
here, from `1` on the page). Besides reflexivity, `v′_i < v″_j` holds when `{v_i, v_j} ∈ E`
(this gives both `v′_i < v″_j` and `v′_j < v″_i`) and when `i < j`. -/
def adjPrec (G : SimpleGraph (Fin n)) (a b : Fin n ⊕ Fin n) : Prop :=
  a = b ∨ ∃ i j : Fin n, a = Sum.inl i ∧ b = Sum.inr j ∧ (G.Adj i j ∨ i < j)

/-- `adjPrec G` is a partial order: every strict relation goes from a job `v′_i` to a job `v″_j`,
so there are no chains of length two and transitivity is immediate. -/
theorem adjPrec_isPartialOrder (G : SimpleGraph (Fin n)) :
    IsPartialOrder (Fin n ⊕ Fin n) (adjPrec G) where
  refl a := Or.inl rfl
  trans a b c hab hbc := by
    rcases hab with rfl | ⟨i, j, rfl, rfl, h⟩
    · exact hbc
    · rcases hbc with rfl | ⟨i', j', h1, -, -⟩
      · exact Or.inr ⟨i, j, rfl, rfl, h⟩
      · exact absurd h1 Sum.inr_ne_inl
  antisymm a b hab hba := by
    rcases hab with h | ⟨i, j, rfl, rfl, -⟩
    · exact h
    · rcases hba with h | ⟨i', j', h1, -, -⟩
      · exact h.symm
      · exact absurd h1 Sum.inr_ne_inl

/-- The scheduling instance `S` built from a vertex cover instance `G = (V, E)` with
`V = {v_1, …, v_n}` and a parameter `k > 0` (proof of Theorem 8.1, p. 664). For each vertex
`v_i` there are two jobs: `v′_i` with processing time `1/k^i` and weight `0`, and `v″_i` with
processing time `0` and weight `k^i`. Here `i : Fin n` stands for `v_{i+1}`, so the exponent is
`i + 1`. The precedence constraints are `adjPrec G`. -/
noncomputable def adjacencyInstance (G : SimpleGraph (Fin n)) (k : ℝ≥0) :
    Instance (Fin n ⊕ Fin n) where
  P := adjPrec G
  isPartialOrder := adjPrec_isPartialOrder G
  p := Sum.elim (fun i => ((k : ℝ) ^ ((i : ℕ) + 1))⁻¹) (fun _ => 0)
  w := Sum.elim (fun _ => 0) (fun i => (k : ℝ) ^ ((i : ℕ) + 1))
  p_nonneg j := by cases j <;> simp
  w_nonneg j := by cases j <;> simp

/-- The pair `(v′_i, v″_i)` is incomparable in `S`: there is no edge `{v_i, v_i}` (a simple
graph has no loops) and not `i < i`, and nothing precedes a job `v′_j`. -/
theorem heavy_incomparable (G : SimpleGraph (Fin n)) (i : Fin n) :
    Incomparable (adjPrec G) (Sum.inl i) (Sum.inr i) := by
  refine ⟨?_, ?_⟩
  · rintro (h | ⟨a, b, ha, hb, h⟩)
    · exact Sum.inl_ne_inr h
    · cases ha; cases hb; exact h.elim (G.irrefl) (lt_irrefl _)
  · rintro (h | ⟨a, b, ha, -, -⟩)
    · exact Sum.inr_ne_inl h
    · exact Sum.inr_ne_inl ha

/-- The node `(v′_i, v″_i)` of `G^S_P` for the instance `S = adjacencyInstance G k`: these `n`
nodes are the "heavy" ones, of weight `k^{-i} · k^i = 1`. -/
def heavy (G : SimpleGraph (Fin n)) (k : ℝ≥0) (i : Fin n) :
    IncPair (adjacencyInstance G k).P :=
  ⟨(Sum.inl i, Sum.inr i), heavy_incomparable G i⟩

end SingleMachinePrec.VariableCost
