import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **Theorem 4.2** — El Ghaoui & Lebret (1997), §4.2, p. 1045 (PDF p. 11). When `ρ = 1`, the
Euclidean-norm SRLS can be solved by computing an optimal solution `(λ, τ, x)` of the SDP (32)
"minimize `λ` subject to `[λ − τ, 0, (A₀x − b₀)ᵀ; 0, τI, M(x)ᵀ; A₀x − b₀, M(x), I] ⪰ 0`".
Made precise as:
(a) for every `x` and `λ`, some `τ` makes `(λ, τ, x)` feasible for (32) iff `r_S(A, b, x)² ≤ λ`;
(b) `(λ, τ, x)` is an optimal solution of (32) iff `x` is an SRLS solution (minimizes
`r_S(A, b, ·)` over `ℝ^m`), `λ = r_S(A, b, x)²` and `(λ, τ, x)` is feasible for (32).
The hypothesis `1 ≤ p` is not written in the paper but is needed: for `p = 0` the `τI` block is
empty and every `λ` is feasible for (32) (take `τ` very negative). -/
theorem srls_sdp_exact {n m p : ℕ} (hp : 1 ≤ p) (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ) :
    (∀ (x : Fin m → ℝ) (lam : ℝ),
        (∃ τ : ℝ, SDP32Feasible A0 A b0 b lam τ x) ↔ rS A0 A b0 b 1 x ^ 2 ≤ lam) ∧
      ∀ (lam τ : ℝ) (x : Fin m → ℝ),
        SDP32Optimal A0 A b0 b lam τ x ↔
          IsSRLSSolution A0 A b0 b 1 x ∧ lam = rS A0 A b0 b 1 x ^ 2 ∧
            SDP32Feasible A0 A b0 b lam τ x := by sorry

end RobustLS.Structured
