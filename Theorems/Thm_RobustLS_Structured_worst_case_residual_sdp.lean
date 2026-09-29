import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **Theorem 4.1, first assertion (the two-variable SDP)** — El Ghaoui & Lebret (1997), §4.1,
p. 1045 (PDF p. 11). For every fixed `x`, the squared worst-case residual (for `ρ = 1`)
`r_S(A, b, x)²` is the optimal value of the SDP in two variables "minimize `λ` subject to (29)":
every `λ` for which some `τ` makes `𝓕(λ, τ) ⪰ 0` satisfies `λ ≥ r_S(A, b, x)²`, and
`λ = r_S(A, b, x)²` is feasible (the minimum is attained).
The paper's second and third assertions ((30)–(31) and the worst-case `δ`) are not formalized.
The hypothesis `1 ≤ p` is not written in the paper but is needed: for `p = 0` every `λ` is
feasible for (29). -/
theorem worst_case_residual_sdp {n m p : ℕ} (hp : 1 ≤ p) (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) :
    (∀ lam τ : ℝ, (calF A0 A b0 b x lam τ).PosSemidef → rS A0 A b0 b 1 x ^ 2 ≤ lam) ∧
      ∃ τ : ℝ, (calF A0 A b0 b x (rS A0 A b0 b 1 x ^ 2) τ).PosSemidef := by sorry

end RobustLS.Structured
