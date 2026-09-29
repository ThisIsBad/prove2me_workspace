import Mathlib

open Matrix

namespace ConjGrad.Termination

/-- The data carried by one step of the conjugate gradient method (Hestenes–Stiefel 1952,
§3, p. 411): the current estimate `x = xᵢ` of the solution `h`, its residual `r = rᵢ`, and
the current direction `p = pᵢ`. Vectors are `Fin n → ℝ`. -/
structure CGState (n : ℕ) where
  /-- the estimate `xᵢ` of the solution `h` -/
  x : Fin n → ℝ
  /-- the residual `rᵢ` -/
  r : Fin n → ℝ
  /-- the direction `pᵢ` -/
  p : Fin n → ℝ

/-- The step length (3:1b): `aᵢ = |rᵢ|² / (pᵢ, Apᵢ)`. Lean's real division returns `0` when
`(pᵢ, Apᵢ) = 0`. -/
noncomputable def cgA {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) : ℝ :=
  (s.r ⬝ᵥ s.r) / (s.p ⬝ᵥ (A *ᵥ s.p))

/-- One general routine step of the cg-method, formulas (3:1b)–(3:1f) in this order:
`aᵢ = |rᵢ|²/(pᵢ,Apᵢ)`, `xᵢ₊₁ = xᵢ + aᵢpᵢ`, `rᵢ₊₁ = rᵢ − aᵢApᵢ`, `bᵢ = |rᵢ₊₁|²/|rᵢ|²`,
`pᵢ₊₁ = rᵢ₊₁ + bᵢpᵢ`. There is no stopping test: once `rₘ = 0` the division by zero gives
`bₘ₋₁ = 0`, `pₘ = 0`, `aₘ = 0`, and the iteration stays at `xₘ` with zero residual and
direction. -/
noncomputable def cgStep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) : CGState n :=
  let a := cgA A s                           -- (3:1b)
  let x' := s.x + a • s.p                    -- (3:1c)
  let r' := s.r - a • (A *ᵥ s.p)             -- (3:1d)
  let b := (r' ⬝ᵥ r') / (s.r ⬝ᵥ s.r)         -- (3:1e)
  let p' := r' + b • s.p                     -- (3:1f)
  ⟨x', r', p'⟩

/-- The cg-method (3:1) started at an arbitrary estimate `x₀`: step `0` is (3:1a),
`p₀ = r₀ = k − Ax₀`, and step `i + 1` applies `cgStep` to step `i`. Indices are 0-based as
in the paper. -/
noncomputable def cgIter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k x₀ : Fin n → ℝ) :
    ℕ → CGState n
  | 0 => ⟨x₀, k - A *ᵥ x₀, k - A *ᵥ x₀⟩
  | i + 1 => cgStep A (cgIter A k x₀ i)

end ConjGrad.Termination
