import Mathlib

namespace KendallBD.Cumul

/-- The discriminant of the quadratic (49), `λ₀ w z² − (λ₀ + μ₀) z + μ₀ = 0`, in `z`:
`(λ₀ + μ₀)² − 4 λ₀ μ₀ w`. -/
noncomputable def disc (lam0 mu0 w : ℝ) : ℝ :=
  (lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w

/-- The smaller root `α` of (49): `(λ₀ + μ₀ − √disc) / (2 λ₀ w)`. -/
noncomputable def alpha (lam0 mu0 w : ℝ) : ℝ :=
  (lam0 + mu0 - Real.sqrt (disc lam0 mu0 w)) / (2 * lam0 * w)

/-- The larger root `β` of (49): `(λ₀ + μ₀ + √disc) / (2 λ₀ w)`. -/
noncomputable def beta (lam0 mu0 w : ℝ) : ℝ :=
  (lam0 + mu0 + Real.sqrt (disc lam0 mu0 w)) / (2 * lam0 * w)

/-- Kendall's explicit generating function (50):
`ψ(z, w, t) = w · (α(β − z) + β(z − α) e^{−λ₀ w (β − α) t}) / ((β − z) + (z − α) e^{−λ₀ w (β − α) t})`. -/
noncomputable def psi (lam0 mu0 z w t : ℝ) : ℝ :=
  w * ((alpha lam0 mu0 w * (beta lam0 mu0 w - z)
        + beta lam0 mu0 w * (z - alpha lam0 mu0 w)
          * Real.exp (-lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w) * t))
      / ((beta lam0 mu0 w - z)
        + (z - alpha lam0 mu0 w)
          * Real.exp (-lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w) * t)))

/-- The parameter (53): `x = 4 λ₀ μ₀ / (λ₀ + μ₀)²`. -/
noncomputable def x (lam0 mu0 : ℝ) : ℝ :=
  4 * lam0 * mu0 / (lam0 + mu0) ^ 2

/-- The law (52) of the cumulative population `M_∞`:
`Q_M = ((λ₀ + μ₀)/(2λ₀)) · ((2M)!/(2^{2M}(M!)²)) · (x^M/(2M − 1))` for `M = 1, 2, 3, …`,
and `Q_0 = 0` (the cumulative population is at least its initial value `M_0 = 1`). -/
noncomputable def Q (lam0 mu0 : ℝ) (M : ℕ) : ℝ :=
  if M = 0 then 0
  else (lam0 + mu0) / (2 * lam0)
    * ((Nat.factorial (2 * M) : ℝ) / (2 ^ (2 * M) * (Nat.factorial M : ℝ) ^ 2))
    * (x lam0 mu0 ^ M / (2 * (M : ℝ) - 1))

/-- The partial differential equation (31) with constant rates `λ₀, μ₀`, at one point `(z, w, t)`:
both partial derivatives of `ψ` exist there (as genuine derivatives) and
`∂ψ/∂t = (λ₀ w z² − (λ₀ + μ₀) z + μ₀) ∂ψ/∂z`. -/
def SolvesPDE (lam0 mu0 : ℝ) (ψ : ℝ → ℝ → ℝ → ℝ) (z w t : ℝ) : Prop :=
  ∃ a b : ℝ, HasDerivAt (fun s => ψ z w s) a t ∧ HasDerivAt (fun y => ψ y w t) b z ∧
    a = (lam0 * w * z ^ 2 - (lam0 + mu0) * z + mu0) * b

end KendallBD.Cumul
