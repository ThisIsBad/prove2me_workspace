import Mathlib
import Definitions.Def_LimitedBFGS_SQN_specialH
import Definitions.Def_LimitedBFGS_SQN_quadratic

open Matrix

namespace LimitedBFGS.SQN

/-- State of the SQN iteration: the current iterate `x` and the stored window of correction
pairs `(s_j, y_j)` (at most `m` of them, oldest first). -/
structure SQNState (n : ℕ) where
  /-- the current iterate `x_k` -/
  x : Fin n → ℝ
  /-- the stored pairs `(s_j, y_j)`, `j = k − min(k, m), …, k − 1`, oldest first -/
  pairs : List ((Fin n → ℝ) × (Fin n → ℝ))

/-- The SQN search direction `d = −H g`, where `H` is the special BFGS matrix (4)–(5) built
from `H₀` and the stored pairs, and `g = A x + b` (Nocedal 1980, p. 778, (17)). -/
noncomputable def sqnDir {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (st : SQNState n) : Fin n → ℝ :=
  -(specialHList H₀ st.pairs *ᵥ grad A b st.x)

/-- The SQN iteration (17) (Nocedal 1980, p. 778) on `f(x) = ½ xᵀAx + bᵀx` with exact line
searches, `m` stored corrections and initial matrix `H₀`, started at `x₀` (0-based):
`d_i = −H_i g_i`, `x_{i+1} = x_i + α_i d_i`, and `H_{i+1} = F(s_i, y_i, H_i)` is the special
BFGS matrix (4)–(5), i.e. `H₀` updated by the last `min(i + 1, m)` pairs
`s_j = x_{j+1} − x_j`, `y_j = g_{j+1} − g_j`. The new pair is appended and the oldest one dropped
once more than `m` are stored. There is no stopping rule: after `g_k = 0`, `d_k = 0`,
`α_k = 0`, the pair `(0, 0)` is stored (a no-op in `bfgsStep`), and the iterate stays put. -/
noncomputable def sqnIter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (x₀ : Fin n → ℝ) : ℕ → SQNState n
  | 0 => ⟨x₀, []⟩
  | k + 1 =>
    let st := sqnIter A b H₀ m x₀ k
    let d := sqnDir A b H₀ st
    let x' := st.x + exactStep A b st.x d • d
    let pairs' := st.pairs ++ [(x' - st.x, grad A b x' - grad A b st.x)]
    ⟨x', pairs'.drop (pairs'.length - m)⟩

end LimitedBFGS.SQN
