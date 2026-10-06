import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Proposition 4.2.1 (Bäuerle–Rieder, p. 80, PDF 94). Under Assumption (FM) (no arbitrage, in
the model; `𝔼‖R_n‖ < ∞`, `hFM2`), the function `b(x) := 1+x` is an upper bounding function for
the Markov Decision Model: there exist `c_r, c_g, α_b ≥ 0` with (i) `r_n^+ ≤ c_r b` (trivial,
`r_n ≡ 0`); (ii) `g_N^+ = U^+ ≤ c_g b` on `E = domU`; (iii)
`𝔼[b((1+i_{n+1})(x+a·R_{n+1}))] ≤ α_b b(x)` for all `n < N`, `x ∈ E`, `a ∈ D_n(x)`. -/
theorem upper_bounding_function {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d)
    (hdomU : M.domU = Set.Ici (0 : ℝ) ∨ M.domU = Set.Ioi (0 : ℝ)) (hFM2 : M.FM2) :
    ∃ cr cg αb : ℝ, 0 ≤ cr ∧ 0 ≤ cg ∧ 0 ≤ αb ∧
      (∀ n < M.N, ∀ x ∈ M.domU, max (0 : ℝ) 0 ≤ cr * (1 + x)) ∧
      (∀ x ∈ M.domU, max (M.U x) 0 ≤ cg * (1 + x)) ∧
      (∀ n < M.N, ∀ x ∈ M.domU, ∀ a ∈ M.D n x,
        (∫ ω, (1 + (1 + M.i (n + 1)) * (x + ∑ k, a k * M.R (n + 1) ω k)) ∂M.measIP) ≤
          αb * (1 + x)) := by sorry

end MDPFinance.TerminalWealth

