import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic

open scoped InnerProductSpace

namespace SparseApprox.Greedy

/-- The state of Algorithm Greedy at the start of an iteration: the columns `a_j⁽ʳ⁾` of `A⁽ʳ⁾`,
the vector `b⁽ʳ⁾`, and the set `τ` of indices chosen so far. -/
structure State (m n : ℕ) where
  col : Fin n → EuclideanSpace ℝ (Fin m)
  res : EuclideanSpace ℝ (Fin m)
  chosen : Finset (Fin n)

/-- The initial state: `A⁽⁰⁾ = A` (bold: columns normalized), `b⁽⁰⁾ = b`, `τ = ∅`. -/
noncomputable def initState {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) : State m n :=
  ⟨fun j => normalizeVec (colE A j), b, ∅⟩

/-- One iteration of the selection phase with chosen index `k`, `a = a_k⁽ʳ⁾`:
`b⁽ʳ⁺¹⁾ = b⁽ʳ⁾ − (aᵀb⁽ʳ⁾) a`, `τ ← τ ∪ {k}`, and for `j` outside the new `τ`,
`a_j⁽ʳ⁺¹⁾ = normalize(a_j⁽ʳ⁾ − (aᵀa_j⁽ʳ⁾) a)`; columns with index in the new `τ` are left
unchanged, as in the pseudo-code. -/
noncomputable def greedyStep {m n : ℕ} (s : State m n) (k : Fin n) : State m n :=
  { col := fun j =>
      if j ∈ insert k s.chosen then s.col j
      else normalizeVec (s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k)
    res := s.res - ⟪s.col k, s.res⟫_ℝ • s.col k
    chosen := insert k s.chosen }

/-- The state at the start of iteration `r` when the indices chosen at iterations
`0, 1, …` are `k 0, k 1, …`. -/
noncomputable def greedyState {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (k : ℕ → Fin n) : ℕ → State m n
  | 0 => initState A b
  | r + 1 => greedyStep (greedyState A b k r) (k r)

/-- The choices `k 0, …, k (t-1)` are a run of `t` iterations of the selection phase of
Algorithm Greedy on input `A, b, ε`: at every iteration `r < t`, with state `s`,
the while-condition `‖b⁽ʳ⁾‖₂ > ε` holds, the "no solution exists" exit is not taken
(`a_k⁽ʳ⁾ᵀb⁽ʳ⁾ ≠ 0`), `k r ∉ τ`, and `|a_k⁽ʳ⁾ᵀb⁽ʳ⁾|` is maximum over `j ∉ τ`. -/
def IsGreedyRun {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (ε : ℝ) (k : ℕ → Fin n) (t : ℕ) : Prop :=
  ∀ r < t,
    ε < ‖(greedyState A b k r).res‖ ∧
    k r ∉ (greedyState A b k r).chosen ∧
    ⟪(greedyState A b k r).col (k r), (greedyState A b k r).res⟫_ℝ ≠ 0 ∧
    ∀ j ∉ (greedyState A b k r).chosen,
      |⟪(greedyState A b k r).col j, (greedyState A b k r).res⟫_ℝ| ≤
        |⟪(greedyState A b k r).col (k r), (greedyState A b k r).res⟫_ℝ|

end SparseApprox.Greedy
