import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary
import Definitions.Def_MDPFinance_MeanVariance_QPValueFunction

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Theorem 4.6.5 (Bäuerle–Rieder, p. 121, PDF 135). Let `(d_n)` be as in Eq. (4.34) (`d_N := 1`,
`d_n := d_{n+1}(1-ℓ_{n+1})`). For the Markov Decision Problem `QP(b)`: a) the value functions are
`V_n(x) = (xS⁰_N/S⁰_n - b)^2 d_n`, and `V_0(x_0)` is the value of `QP(b)`; b) the optimal policy
`π^* = (f_0^*,…,f_{N-1}^*)` is `f_n^*(x) = (bS⁰_n/S⁰_N - x) C_{n+1}^{-1}𝔼[R_{n+1}]` (admissible
and optimal for `QP(b)`); c) the first and second moments of `X_N` under `π^*` are
`𝔼^{π^*}_{x_0}[X_N] = x_0S⁰_Nd_0 + b(1-d_0)`, `𝔼^{π^*}_{x_0}[X_N^2] = (x_0S⁰_N)^2d_0 + b^2(1-d_0)`. -/
theorem qp_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d) (b : ℝ)
    (dseq : ℕ → ℝ) (hdN : dseq M.N = 1)
    (hdrec : ∀ n < M.N, dseq n = dseq (n + 1) * (1 - M.ell (n + 1))) :
    (∀ n ≤ M.N, ∀ x : ℝ, M.VQP b n x = (x * M.S0 M.N / M.S0 n - b) ^ 2 * dseq n) ∧
      (∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
        (∀ n < M.N, ∀ x : ℝ, fstar n x =
          fun k => (b * M.S0 n / M.S0 M.N - x) * ((M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1)) k)) ∧
        M.IsOptimalQP b fstar ∧
        M.meanXN fstar = M.x0 * M.S0 M.N * dseq 0 + b * (1 - dseq 0) ∧
        M.meanXNsq fstar = (M.x0 * M.S0 M.N) ^ 2 * dseq 0 + b ^ 2 * (1 - dseq 0)) := by sorry

end MDPFinance.MeanVariance
