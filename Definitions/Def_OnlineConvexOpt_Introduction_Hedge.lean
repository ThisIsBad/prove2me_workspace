import Mathlib

namespace OnlineConvexOpt.Introduction

variable {N : ℕ}

/-- One run of the Hedge algorithm (Algorithm 1, p. 12) with `N` experts and learning rate
`ε`, against an adversarially chosen non-negative loss sequence `ℓ : ℕ → Fin N → ℝ`
(`ℓ_t(i)` is expert `i`'s loss at round `t`). `W` are the weights (`W_1(i) = 1`, updated as
`W_{t+1}(i) = W_t(i) e^{-ε ℓ_t(i)}`); `x` is Hedge's mixed strategy, the weights normalized to
a probability vector, `x_t(i) = W_t(i) / ∑_j W_t(j)`. -/
structure IsHedgeRun (ε : ℝ) (ℓ : ℕ → Fin N → ℝ) (W : ℕ → Fin N → ℝ)
    (x : ℕ → Fin N → ℝ) : Prop where
  weight_init : ∀ i, W 0 i = 1
  weight_update : ∀ t i, W (t + 1) i = W t i * Real.exp (-ε * ℓ t i)
  prob_def : ∀ t i, x t i = W t i / ∑ j, W t j

/-- Hedge's cumulative expected loss over rounds `0, …, T - 1`,
`∑_{t=1}^T x_t^\top \ell_t` in the book's vector notation, p. 12. -/
noncomputable def expectedLoss {N : ℕ} (x ℓ : ℕ → Fin N → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ i, x t i * ℓ t i

/-- Expert `i`'s cumulative loss over rounds `0, …, T - 1`, `∑_{t=1}^T \ell_t(i)`. -/
noncomputable def expertLoss {N : ℕ} (ℓ : ℕ → Fin N → ℝ) (i : Fin N) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, ℓ t i

end OnlineConvexOpt.Introduction
