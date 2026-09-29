import Mathlib
import Definitions.Def_ConjGrad_Termination_cgIter

open Matrix

namespace ConjGrad.Termination

/-- Theorems 4:2 and 5:2 (Hestenes–Stiefel 1952, pp. 410, 412, 415): for a symmetric
positive definite `n × n` matrix `A`, a right-hand side `k` with solution `h` (`Ah = k`) and
an arbitrary initial estimate `x₀`, the cg-method (3:1) reaches the solution after at most
`n` steps: some estimate `xₘ` with `m ≤ n` equals `h`. -/
theorem cg_terminates_in_n_steps {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k h : Fin n → ℝ) (hh : A *ᵥ h = k) (x₀ : Fin n → ℝ) :
    ∃ m ≤ n, (cgIter A k x₀ m).x = h := by sorry

end ConjGrad.Termination
