import Mathlib
import Definitions.Def_FracPackCover_General_Basic

namespace FracPackCover.General

/-!
# Procedure IMPROVE-GENERAL (Figure 4, p. 25), with corrected step parameters

Figure 4 prints `α = 4λ₀⁻¹ ln(6mρλ₀⁻¹)` and `σ = λ₀/(24αρ²)`. These do not meet the hypotheses
of Lemmas 4.2 and 4.3 (which need `α ≥ 2λ⁻¹ ln(6mρλ⁻¹)` and `σ ≤ λ/(24αρ²)` for the *current* `λ`)
when `λ₀/2 ≤ λ < λ₀`, although the loop runs for all `λ ≥ λ₀/2`. This development uses the
paper's formulas with `λ₀/2` in place of `λ₀`:
`α = 4λ₀⁻¹ ln(12mρλ₀⁻¹)` and `σ = λ₀/(48αρ²)`.
-/

/-- Corrected step parameter `α = 4λ₀⁻¹ ln(12 m ρ λ₀⁻¹)` (Figure 4 prints `6` for `12`). -/
noncomputable def alphaGen (m : ℕ) (ρ lam0 : ℝ) : ℝ :=
  4 / lam0 * Real.log (12 * m * ρ / lam0)

/-- Corrected step size `σ = λ₀/(48 α ρ²)` (Figure 4 prints `24` for `48`). -/
noncomputable def sigmaGen (m : ℕ) (ρ lam0 : ℝ) : ℝ :=
  lam0 / (48 * alphaGen m ρ lam0 * ρ ^ 2)

/-- How a run of IMPROVE-GENERAL ended. -/
inductive ImproveExit
  /-- the loop test failed because `max_i (a_i x − b_i)/d_i < λ₀/2` -/
  | lambdaHalved
  /-- the loop test failed because `x` and `y` satisfy (𝒢2) (while `λ ≥ λ₀/2`) -/
  | relaxedOpt
  /-- the fuel bound was reached with the loop test still true -/
  | outOfFuel
  deriving DecidableEq

/-- Output of a (fuelled) run: the returned point, the number of oracle calls made, how it ended. -/
structure ImproveResult (n : ℕ) where
  point : Fin n → ℝ
  calls : ℕ
  exit : ImproveExit

open Classical in
/-- The while-loop of Figure 4 with fixed `λ₀, α, σ`, run for at most `fuel` evaluations of the
loop test. An evaluation of the test that reaches the (𝒢2) conjunct computes `y` and calls the
oracle once (`x̃ = orc y`, which gives `C_𝒢(y) = y^t(Ax̃ − b)`); if the test holds, the body reuses
that `x̃` for the update `x ← (1 − σ)x + σx̃`. A test that fails at `λ(x) < λ₀/2` makes no call. -/
noncomputable def improveLoop {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (lam0 α σ : ℝ) :
    ℕ → (Fin n → ℝ) → ImproveResult n
  | 0, x => ⟨x, 0, .outOfFuel⟩
  | k + 1, x =>
    if lam A b d x < lam0 / 2 then ⟨x, 0, .lambdaHalved⟩
    else
      let y := dualVec A b d α x
      let xt := orc y
      if G2 A b d x (lam A b d x) y (lagr A b y xt) then ⟨x, 1, .relaxedOpt⟩
      else
        let r := improveLoop A b d orc lam0 α σ k ((1 - σ) • x + σ • xt)
        ⟨r.point, r.calls + 1, r.exit⟩

/-- IMPROVE-GENERAL(x₀) with fuel: `λ₀ = λ(x₀)`, `α = alphaGen m ρ λ₀`, `σ = sigmaGen m ρ λ₀`
(the corrected parameters), then the loop of Figure 4. -/
noncomputable def improveGeneral {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (ρ : ℝ) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (fuel : ℕ)
    (x0 : Fin n → ℝ) : ImproveResult n :=
  improveLoop A b d orc (lam A b d x0) (alphaGen m ρ (lam A b d x0))
    (sigmaGen m ρ (lam A b d x0)) fuel x0

end FracPackCover.General
