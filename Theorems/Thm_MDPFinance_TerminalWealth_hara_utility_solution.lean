import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market
import Definitions.Def_MDPFinance_TerminalWealth_PowerAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Theorem 4.2.11 (Bäuerle–Rieder, p. 88, PDF 102). Under Assumption (FM) (`hFM2`), let
`U(x) = (x+b)^γ` be the HARA utility with `b ≥ 0`, `0 < γ < 1`, `domU = [-b,∞)`. With
`E_n := {x | x·S⁰_N/S⁰_n + b ≥ 0}`: a) the value functions are `V_n(x) = d_n(x·S⁰_N/S⁰_n + b)^γ`,
`x ∈ E_n`, with `d_N = 1` and `d_n = ∏_{k=n}^{N-1} v_k` (`v_k` the value of problem (4.7)); b) the
optimal amounts invested in the stocks are `f_n^*(x) = α_n^*(x + bS⁰_n/S⁰_N)`, `x ∈ E_n`, where
`α_n^*` is the optimal solution of (4.7); the optimal portfolio strategy is
`(f_0^*,…,f_{N-1}^*)`. -/
theorem hara_utility_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2) (γ b : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hb : 0 ≤ b) (hdomU : M.domU = Set.Ici (-b))
    (hU : ∀ x, -b ≤ x → M.U x = (x + b) ^ γ)
    (En : ℕ → Set ℝ) (hEn : ∀ n, En n = {x | 0 ≤ x * M.S0 M.N / M.S0 n + b}) :
    (∀ n ≤ M.N, ∀ x ∈ En n,
        M.V n x = (((∏ k ∈ Finset.Ico n M.N, M.vPower γ k) *
          (x * M.S0 M.N / M.S0 n + b) ^ γ : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.Afrac n ∧
          ∫ ω, (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ^ γ ∂M.measIP = M.vPower γ n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x ∈ En n,
            fstar n x = fun k => αstar n k * (x + b * M.S0 n / M.S0 M.N)) ∧
          ∀ x ∈ En 0, M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.TerminalWealth
