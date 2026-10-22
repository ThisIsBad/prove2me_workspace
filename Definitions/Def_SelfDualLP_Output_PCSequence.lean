import Mathlib
import Definitions.Def_SelfDualLP_Output_Neighborhood

open Matrix

namespace SelfDualLP.Output

/-- The algorithm's parameter `β = 1/4` (p. 60): predictor steps start in `𝒩(β)` and stay in
`𝒩(2β)`. -/
noncomputable def beta : ℝ := 1 / 4

/-- The initial point `(y⁰, x⁰, τ⁰, θ⁰, s⁰, κ⁰) = (0, e, 1, 1, e, 1)` (Theorem 2 (ii) under (7)). -/
def initialPoint (m n : ℕ) : HLPPoint m n :=
  ⟨0, ones n, 1, 1, ones n, 1⟩

/-- `d` solves the linear system (11)–(12) at `z` with parameter `γ`:
`d ∈ Q`, `X d_s + S d_x = γμe − Xs` componentwise, and `τ d_κ + κ d_τ = γμ − τκ`,
with `μ = (xᵀs + τκ)/(n + 1)` evaluated at `z`. -/
def IsPCDirection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z d : HLPPoint m n) (γ : ℝ) : Prop :=
  InQ7 A b c d ∧
  (∀ j, z.x j * d.s j + z.s j * d.x j = γ * mu z - z.x j * z.s j) ∧
  z.τ * d.κ + z.κ * d.τ = γ * mu z - z.τ * z.κ

/-- `z` is a sequence of iterates of the Mizuno–Todd–Ye predictor–corrector algorithm applied to
(HLP) under (7) (pp. 60–61), read as a relation:
* `z 0 = (0, e, 1, 1, e, 1)`;
* for even `k` (predictor step) there are a solution `d` of (11)–(12) with `γ = 0` and the step
  `ᾱ = max {α : z k + α d ∈ 𝒩(2β)}` (13) — the maximum must exist — with `z (k+1) = z k + ᾱ d`;
* for odd `k` (corrector step) there is a solution `d` of (11)–(12) with `γ = 1` and
  `z (k+1) = z k + d`. -/
def IsPCSequence {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : ℕ → HLPPoint m n) : Prop :=
  z 0 = initialPoint m n ∧
  ∀ k, ∃ d : HLPPoint m n,
    (Even k ∧ IsPCDirection A b c (z k) d 0 ∧
      ∃ α : ℝ, IsGreatest {a : ℝ | Nbhd A b c (2 * beta) ((z k).move d a)} α ∧
        z (k + 1) = (z k).move d α) ∨
    (¬ Even k ∧ IsPCDirection A b c (z k) d 1 ∧ z (k + 1) = (z k).move d 1)

end SelfDualLP.Output
