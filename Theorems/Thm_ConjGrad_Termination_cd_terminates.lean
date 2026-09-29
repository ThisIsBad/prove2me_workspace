import Mathlib
import Definitions.Def_ConjGrad_Termination_IsCDRun

open Matrix

namespace ConjGrad.Termination

/-- Theorem 4:2 (Hestenes–Stiefel 1952, p. 412). The cd-method is an `m`-step method with
`m ≤ n`: for a symmetric positive definite `n × n` matrix `A`, the solution `h` of `Ah = k`,
and every run of the cd-method whose directions `p₀, …, pₙ₋₁` are nonzero, some estimate
`xₘ` with `m ≤ n` equals `h`. -/
theorem cd_terminates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k h : Fin n → ℝ) (hh : A *ᵥ h = k) (x r p : ℕ → Fin n → ℝ) (hcd : IsCDRun A k x r p)
    (hp : ∀ i < n, p i ≠ 0) :
    ∃ m ≤ n, x m = h := by sorry

end ConjGrad.Termination
