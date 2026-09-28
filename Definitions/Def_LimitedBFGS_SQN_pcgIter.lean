import Mathlib
import Definitions.Def_LimitedBFGS_SQN_quadratic

open Matrix

namespace LimitedBFGS.SQN

/-- State of the preconditioned conjugate gradient iteration: iterate `x` and direction `d`. -/
structure PCGState (n : ℕ) where
  /-- the current iterate `x_k` -/
  x : Fin n → ℝ
  /-- the current search direction `d_k` -/
  d : Fin n → ℝ

/-- The PCG with fixed preconditioner `H₀` (Nocedal 1980, p. 777: iteration (13) with `H₀` in
place of every `H_{i−1}`, cf. (14)) on `f(x) = ½ xᵀAx + bᵀx` with exact line searches, started at
`x₀` (0-based): `d₀ = −H₀ g₀`, `x_{i+1} = x_i + α_i d_i`,
`d_{i+1} = −H₀ g_{i+1} + β_{i+1} d_i` with `β_{i+1} = y_iᵀ H₀ g_{i+1} / y_iᵀ d_i` and
`y_i = g_{i+1} − g_i`. (The denominator `y_iᵀ d_i` corrects the printed `y_{i−1}ᵀ d_i` of (13),
following (12) and p. 778.) After `g_k = 0`, `β = 0`, all later directions are `0`, and the
iterate stays put. -/
noncomputable def pcgIter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) : ℕ → PCGState n
  | 0 => ⟨x₀, -(H₀ *ᵥ grad A b x₀)⟩
  | k + 1 =>
    let st := pcgIter A b H₀ x₀ k
    let x' := st.x + exactStep A b st.x st.d • st.d
    let y := grad A b x' - grad A b st.x
    let β := (y ⬝ᵥ (H₀ *ᵥ grad A b x')) / (y ⬝ᵥ st.d)
    ⟨x', -(H₀ *ᵥ grad A b x') + β • st.d⟩

end LimitedBFGS.SQN
