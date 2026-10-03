import Mathlib
import Definitions.Def_MDPFinance_Stationary_NSValueFunction
import Definitions.Def_MDPFinance_Stationary_LQHelpers

open MeasureTheory
open scoped Matrix

namespace MDPFinance.Stationary

/-- Theorem 2.6.3 (Bäuerle–Rieder, p. 52, PDF 67), the stochastic linear-quadratic problem.
`M` is the non-stationary Markov Decision Model of §2.6.3 (p. 51, PDF 66): state space
`E := Fin m → ℝ`, action space `A := Fin d → ℝ`, `D_n(x) := A`, disturbance
`Z_{n+1} = (A_{n+1}, B_{n+1})` with joint law `ν_n` on `Matrix (Fin m) (Fin m) ℝ ×
Matrix (Fin m) (Fin d) ℝ` (independent across `n`, finite expectation/covariance), transition
`T_n(x,a,A,B) := Ax + Ba`, reward `r_n(x,a) := -x^⊤ Q_n x`, terminal reward
`g_N(x) := -x^⊤ Q_N x` for deterministic, symmetric, positive definite `Q_0,…,Q_N`, no
discounting (`β = 1`), and the standing assumption that `𝔼[B_{n+1}^⊤ Q B_{n+1}]` is positive
definite for every symmetric positive definite `Q`. a) Let `Q̃_n` be recursively defined by
`Q̃_N := Q_N`, `Q̃_n := Q_n + 𝔼[A_{n+1}^⊤ Q̃_{n+1} A_{n+1}] - 𝔼[A_{n+1}^⊤ Q̃_{n+1} B_{n+1}]
(𝔼[B_{n+1}^⊤ Q̃_{n+1} B_{n+1}])^{-1} 𝔼[B_{n+1}^⊤ Q̃_{n+1} A_{n+1}]`. Then `Q̃_n` is symmetric,
positive semidefinite, and `V_n(x) = x^⊤ Q̃_n x`. b) The optimal policy `(f_0^*,…,f_{N-1}^*)` is
`f_n^*(x) := -(𝔼[B_{n+1}^⊤ Q̃_{n+1} B_{n+1}])^{-1} 𝔼[B_{n+1}^⊤ Q̃_{n+1} A_{n+1}] x`, and it is a
maximizer of `V_{n+1}` at time `n`, an `N`-stage policy, and its value `V_0^{π^*}` equals `V_0`.
The coefficient pairs `(A_{n+1}, B_{n+1}) ∼ ν_{n+1}` have finite expectation and covariance
(`hν_mom`: square-integrable entries), so that the matrix expectations are genuine. -/
theorem stochastic_lq_solution {m d N : ℕ} (M : NSMarkovDecisionModel (Fin m → ℝ) (Fin d → ℝ) N)
    (Qs : ℕ → Matrix (Fin m) (Fin m) ℝ) (hQs_sym : ∀ n ≤ N, (Qs n).IsSymm)
    (hQs_pd : ∀ n ≤ N, (Qs n).PosDef)
    (ν : ℕ → Measure (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ))
    (hPD : ∀ n < N, ∀ Q : Matrix (Fin m) (Fin m) ℝ, Q.IsSymm → Q.PosDef →
      (jointMatMean (ν (n + 1)) (fun A B => Bᵀ * Q * B)).PosDef)
    (hDn : ∀ n < N, M.D n = Set.univ)
    (hν_mom : ∀ n, 1 ≤ n → n ≤ N → (∀ i j, MemLp (fun p => p.1 i j) 2 (ν n)) ∧
      ∀ i j, MemLp (fun p => p.2 i j) 2 (ν n))
    (hQ : ∀ n < N, ∀ x a, M.Q n (x, a) = (ν (n + 1)).map (fun p => p.1.mulVec x + p.2.mulVec a))
    (hr : ∀ n < N, ∀ x a, M.r n (x, a) = -(xQx (Qs n) x))
    (hg : ∀ x, M.g x = -(xQx (Qs N) x))
    (Qtilde : ℕ → Matrix (Fin m) (Fin m) ℝ) (hQtilde_N : Qtilde N = Qs N)
    (hQtilde_rec : ∀ n < N, Qtilde n = Qs n +
      jointMatMean (ν (n + 1)) (fun A _ => Aᵀ * Qtilde (n + 1) * A) -
        jointMatMean (ν (n + 1)) (fun A B => Aᵀ * Qtilde (n + 1) * B) *
          (jointMatMean (ν (n + 1)) (fun _ B => Bᵀ * Qtilde (n + 1) * B))⁻¹ *
            jointMatMean (ν (n + 1)) (fun A B => Bᵀ * Qtilde (n + 1) * A)) :
    (∀ n ≤ N, (Qtilde n).IsSymm ∧ Matrix.PosSemidef (Qtilde n)) ∧
      (∀ n ≤ N, ∀ x, NSV M n x = ((xQx (Qtilde n) x : ℝ) : EReal)) ∧
      (∃ fstar : ℕ → (Fin m → ℝ) → (Fin d → ℝ),
        (∀ n < N, fstar n = fun x =>
          -((jointMatMean (ν (n + 1)) (fun _ B => Bᵀ * Qtilde (n + 1) * B))⁻¹.mulVec
            ((jointMatMean (ν (n + 1)) (fun A B => Bᵀ * Qtilde (n + 1) * A)).mulVec x))) ∧
        (∀ n < N, ∀ x, NSL M n (NSV M (n + 1)) (x, fstar n x) = NST M n (NSV M (n + 1)) x) ∧
        NSIsPolicy M fstar ∧ NSVpi M fstar 0 = NSV M 0) := by sorry

end MDPFinance.Stationary
