import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_PublicGood

namespace MechanismDesign.DominantExamples

/-- Proposition 4.8, p.88. Suppose `N = 2` (agents `0, 1` stand for the book's `1, 2`) and that
the set `{θ ∈ Θ | q(θ) = 1}` is closed. Then a direct public good mechanism is dominant
strategy incentive-compatible, ex post individually rational and ex post (exactly) budget
balanced if and only if there are payments `τ_1, τ_2 ∈ ℝ` with `τ_1 + τ_2 = c` such that for
all `θ ∈ Θ`:
`q(θ) = 1` and `t_i(θ) = τ_i` for both `i` if `θ_1 ≥ τ_1` and `θ_2 ≥ τ_2`;
`q(θ) = 0` and `t_i(θ) = 0` for both `i` otherwise. -/
theorem two_agent_fixed_cost_shares {E : PublicGoodSetting} (M : PublicGoodMechanism E (Fin 2))
    (hclosed : IsClosed {θ : Fin 2 → ℝ | θ ∈ E.typeSpace (Fin 2) ∧ M.q θ = 1}) :
    (M.IsDSIC ∧ M.IsEPIR ∧ M.IsBudgetBalanced) ↔
      ∃ τ : Fin 2 → ℝ, τ 0 + τ 1 = E.c ∧ ∀ θ ∈ E.typeSpace (Fin 2),
        ((τ 0 ≤ θ 0 ∧ τ 1 ≤ θ 1) → M.q θ = 1 ∧ ∀ i, M.t i θ = τ i) ∧
        (¬ (τ 0 ≤ θ 0 ∧ τ 1 ≤ θ 1) → M.q θ = 0 ∧ ∀ i, M.t i θ = 0) := by sorry

end MechanismDesign.DominantExamples

