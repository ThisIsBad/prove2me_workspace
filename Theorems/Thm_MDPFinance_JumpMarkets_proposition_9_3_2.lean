import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket

open MeasureTheory

namespace MDPFinance.JumpMarkets

/-- **Proposition 9.3.2** (p. 284). a) `b(t,x) := e^{γ(T-t)}(1+x)` is a bounding function for
the discrete-time model for all `γ ≥ 0`. b) `α_b ≤ α_γ` **(9.14)** (for `γ + λ ≠ \barμ`, where the
formula is defined); in particular for `γ` large enough `α_γ < 1` and the model is contracting. -/
theorem proposition_9_3_2 {d : ℕ} (M : JumpMarket d) :
    (∀ gamma : ℝ, 0 ≤ gamma → ∃ alpha : ℝ, M.IsBoundingFunction (M.bfun gamma) alpha) ∧
    (∀ gamma : ℝ, 0 ≤ gamma → gamma + M.lam ≠ M.mubar →
      M.IsBoundingFunction (M.bfun gamma) (M.alphaGamma gamma)) ∧
    (∃ gamma0 : ℝ, 0 ≤ gamma0 ∧ ∀ gamma : ℝ, gamma0 ≤ gamma →
      M.alphaGamma gamma < 1 ∧ M.IsBoundingFunction (M.bfun gamma) (M.alphaGamma gamma)) := by sorry

end MDPFinance.JumpMarkets

