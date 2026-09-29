import Mathlib

open Matrix

namespace ConjGrad.ErrorDecrease

/-- The state of the cg-method after `i` steps: the estimate `x = xᵢ` of the solution `h`,
the residual `r = rᵢ` and the direction vector `p = pᵢ`. -/
structure CGState (n : ℕ) where
  /-- the estimate `xᵢ` of `h` -/
  x : Fin n → ℝ
  /-- the residual `rᵢ` -/
  r : Fin n → ℝ
  /-- the direction vector `pᵢ` -/
  p : Fin n → ℝ

/-- The step length `aᵢ = |rᵢ|² / (pᵢ, Apᵢ)` of the cg-method, eq. (5:1b), evaluated at the
state `s = (xᵢ, rᵢ, pᵢ)`. Lean's convention `t / 0 = 0` makes it `0` when `pᵢ = 0`. -/
noncomputable def cgAlpha {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) : ℝ :=
  (s.r ⬝ᵥ s.r) / (s.p ⬝ᵥ (A *ᵥ s.p))

/-- The cg-method (5:1) of Hestenes and Stiefel, 0-based and without a stopping guard:
`p₀ = r₀ = k − Ax₀` (5:1a); then `aᵢ = |rᵢ|²/(pᵢ,Apᵢ)` (5:1b), `xᵢ₊₁ = xᵢ + aᵢpᵢ` (5:1c),
`rᵢ₊₁ = rᵢ − aᵢApᵢ` (5:1d), `bᵢ = |rᵢ₊₁|²/|rᵢ|²` (5:1e), `pᵢ₊₁ = rᵢ₊₁ + bᵢpᵢ` (5:1f).
Once `r_m = 0`, Lean's `t / 0 = 0` makes the sequence stay at `x_m` with `r = p = 0`. -/
noncomputable def cgIter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k x₀ : Fin n → ℝ) :
    ℕ → CGState n
  | 0 => ⟨x₀, k - A *ᵥ x₀, k - A *ᵥ x₀⟩
  | i + 1 =>
    let s := cgIter A k x₀ i
    let a := cgAlpha A s
    let x' := s.x + a • s.p
    let r' := s.r - a • (A *ᵥ s.p)
    let b := (r' ⬝ᵥ r') / (s.r ⬝ᵥ s.r)
    ⟨x', r', r' + b • s.p⟩

end ConjGrad.ErrorDecrease
