import Mathlib
import Definitions.Def_LimitedBFGS_SQN_bfgsStep

open Matrix

namespace LimitedBFGS.SQN

/-- `H₀` updated by the BFGS product form (3) once for each pair `(s, y)` of the list, oldest
(head) first: `specialHList H₀ [(s₀,y₀), …, (s_k,y_k)]` is the right-hand side of (4)
(Nocedal 1980, p. 775). -/
noncomputable def specialHList {n : ℕ} (H₀ : Matrix (Fin n) (Fin n) ℝ)
    (pairs : List ((Fin n → ℝ) × (Fin n → ℝ))) : Matrix (Fin n) (Fin n) ℝ :=
  pairs.foldl (fun H p => bfgsStep H p.1 p.2) H₀

/-- The special BFGS matrix `H_K` of (4)–(5) (Nocedal 1980, p. 775) built from the sequences
`s, y : ℕ → ℝⁿ` with at most `m` stored corrections: `H₀` updated by the pairs
`(s_j, y_j)`, `j = K − min(K, m), …, K − 1`, oldest first. For `K = k + 1 ≤ m` these are
`j = 0, …, k` (formula (4)); for `K = k + 1 > m` they are `j = k − m + 1, …, k` (formula (5)). -/
noncomputable def specialH {n : ℕ} (H₀ : Matrix (Fin n) (Fin n) ℝ) (m : ℕ)
    (s y : ℕ → Fin n → ℝ) (K : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  specialHList H₀
    ((List.range (min K m)).map fun i => (s (K - min K m + i), y (K - min K m + i)))

end LimitedBFGS.SQN
