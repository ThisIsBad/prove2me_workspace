import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The generic one-period exponential-utility sub-problem, Eq. (4.13) (Bäuerle–Rieder, p. 91,
PDF 105): `v_n := inf_{a ∈ ℝ^d} 𝔼[exp(-γ(S⁰_N/S⁰_n) a·R_{n+1})]`. The expectations are Lebesgue
integrals in `[0, ∞]` (no exponential moments are assumed: the book needs only no-arbitrage
here); the infimum lies in `(0, 1]` since `a = 0` gives `1`, and is returned as a real. -/
noncomputable def TerminalWealthMarket.vExp (M : TerminalWealthMarket Ω d) (γ : ℝ) (n : ℕ) :
    ℝ :=
  (⨅ a : Fin d → ℝ,
    ∫⁻ ω, ENNReal.ofReal
      (Real.exp (-γ * (M.S0 M.N / M.S0 n) * ∑ k, a k * M.R (n + 1) ω k)) ∂M.measIP).toReal

end MDPFinance.TerminalWealth
