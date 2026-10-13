import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_TradeExecution

open MeasureTheory
open scoped ENNReal

namespace MDPFinance.JumpMarkets

/-- **Theorem 9.4.2** (p. 296). a) The value function `V(t,x)` is the unique fixed point of
`𝒯` in `IM_cx`. b) There is an optimal Markov strategy `π^*_t = f^*(t, X_{t-})` — the policy
`f(t,x)(s) := f^*(t+s, x)` of the embedded model attains `V` — where `f^*` is the smallest
minimizer **(9.22)** at `V`, and `f^*(t,x) ≤ f^*(t,x+1) ≤ f^*(t,x) + 1`. -/
theorem theorem_9_4_2 (M : TradeExecution) :
    ∃ V : ℝ × ℕ → ℝ, M.IMcx V ∧
      (∀ p ∈ M.E, M.Jinf p = ENNReal.ofReal (V p)) ∧
      (∀ p ∈ M.E, M.T_op V p = V p) ∧
      (∀ v : ℝ × ℕ → ℝ, M.IMcx v → (∀ p ∈ M.E, M.T_op v p = v p) → ∀ p ∈ M.E, v p = V p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ x : ℕ,
        M.fstar V (t, x) ≤ M.fstar V (t, x + 1) ∧
        M.fstar V (t, x + 1) ≤ M.fstar V (t, x) + 1) ∧
      (∃ f : ℕ → ℝ × ℕ → Offer, TradeExecution.IsPolicy f ∧
        (∀ n, ∀ p ∈ M.E, ∀ s : ℝ, 0 ≤ s → (f n p).val s = M.fstar V (p.1 + s, p.2)) ∧
        ∀ p ∈ M.E, M.Jinfpi f p = M.Jinf p) := by sorry

end MDPFinance.JumpMarkets

