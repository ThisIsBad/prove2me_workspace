import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The value function of `QP(b)` from time `n`, state `x`:
`V_n(x) := inf_π 𝔼[(X_N-b)^2 | X_n = x]` over policies admissible from `(n,x)`
(Bäuerle–Rieder, p. 121, PDF 135). -/
noncomputable def MVMarket.VQP (M : MVMarket Ω d) (b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ⨅ π ∈ {π : ℕ → ℝ → (Fin d → ℝ) | M.IsAdmissibleFrom n x π},
    ∫ ω, (M.terminalWealth π (M.N - n) n x ω - b) ^ 2 ∂M.measIP

end MDPFinance.MeanVariance
