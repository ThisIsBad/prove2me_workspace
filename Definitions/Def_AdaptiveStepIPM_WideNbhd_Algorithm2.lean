import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- `(d_x, d_y, d_s)` solves system (2) of §2, p. 4, at `(x, s)` with centering parameter `γ`:
`S d_x + X d_s = γμe − Xs`, `A d_x = 0`, `Aᵀ d_y + d_s = 0`, where `μ = xᵀs/n`. -/
def IsDirection {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  (∀ j, s j * dx j + x j * ds j = γ * AdaptiveStepIPM.PredCorr.mu x s - x j * s j) ∧ A *ᵥ dx = 0 ∧ Aᵀ *ᵥ dy + ds = 0

/-- `p := X^{-0.5} S^{0.5} d_x`, i.e. `p_j = √(s_j / x_j) (d_x)_j` ((6), p. 4). -/
noncomputable def pvec {n : ℕ} (x s dx : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (s j / x j) * dx j

/-- `q := X^{0.5} S^{-0.5} d_s`, i.e. `q_j = √(x_j / s_j) (d_s)_j` ((6), p. 4). -/
noncomputable def qvec {n : ℕ} (x s ds : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (x j / s j) * ds j

/-- `r := (XS)^{-0.5}(γμe − Xs)`, i.e. `r_j = (γμ − x_j s_j) / √(x_j s_j)` ((6), p. 4). -/
noncomputable def rvec {n : ℕ} (γ : ℝ) (x s : Fin n → ℝ) : Fin n → ℝ :=
  fun j => (γ * AdaptiveStepIPM.PredCorr.mu x s - x j * s j) / Real.sqrt (x j * s j)

/-- The admissible step lengths of Algorithm 2 (§4, p. 9): the `θ̄ ≥ 0` such that
`(x(θ), s(θ)) = (x + θ d_x, s + θ d_s) ∈ N` for every `θ ∈ [0, θ̄]` ((3), p. 4). -/
def admissibleSteps {n : ℕ} (N : Set ((Fin n → ℝ) × (Fin n → ℝ))) (x s dx ds : Fin n → ℝ) :
    Set ℝ :=
  {θbar | 0 ≤ θbar ∧ ∀ θ ∈ Set.Icc (0 : ℝ) θbar, (x + θ • dx, s + θ • ds) ∈ N}

/-- One iteration of Algorithm 2 (§4, pp. 9–10) with neighbourhood `N` and parameter `γ`:
from `(x, s)`, take a solution `d` of (2), the largest `θ̄` with `(x(θ), s(θ)) ∈ N` for all
`θ ∈ [0, θ̄]`, and move to `(x⁺, s⁺) = (x(θ̄), s(θ̄))`. -/
def Alg2Step {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (N : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (γ : ℝ) (x s x' s' : Fin n → ℝ) : Prop :=
  ∃ (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (θbar : ℝ),
    IsDirection A x s γ dx dy ds ∧ IsGreatest (admissibleSteps N x s dx ds) θbar ∧
    x' = x + θbar • dx ∧ s' = s + θbar • ds

/-- The step bound `min{1, βγμ / ν}` of Lemma 5 (p. 10), with `ν = ‖AdaptiveStepIPM.PredCorr.Pq‖_∞` (giving `θ₂`) or
`ν = ‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞` (giving `θ₂⁻`). When `ν = 0` the quotient is `+∞` and the minimum is `1`; this
case is made explicit because Lean's real division by zero returns `0`. -/
noncomputable def stepBound (β γ μ ν : ℝ) : ℝ :=
  if ν = 0 then 1 else min 1 (β * γ * μ / ν)

end AdaptiveStepIPM.WideNbhd
