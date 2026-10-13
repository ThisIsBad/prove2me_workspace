import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.2.7** (p. 315), the **One-Step-Look-Ahead Rule**, under (B). Let
`S_0 := {x | g(x) ≥ c(x) + β ∫ g dQ^X(·|x)}` be closed (`Q^X(S_0|x) = 1` for `x ∈ S_0`). Then
a) `f^* = 1_{S_0}` is a maximizer of every `J_n`, `n ≥ 1`, and of `J`; b) with `τ^* := inf{n |
X_n ∈ S_0}`, `τ^* ∧ N` is optimal for the `N`-stage problem, and if `ℙ_x(τ^* < ∞) = 1` for all
`x` then `τ^*` is optimal for the unbounded problem. -/
theorem theorem_10_2_7 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr)
    (S0 : Set E)
    (hS0 : S0 = {x : E | (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (P.g y : EReal)) ≤ (P.g x : EReal)})
    (hclosed : ∀ x ∈ S0, P.QX x S0 = 1) :
    (P.IsMaximizer S0 P.Jlim ∧ ∀ n : ℕ, 1 ≤ n → P.IsMaximizer S0 (P.J n)) ∧
    ((∀ (N : ℕ) (x : E), P.EReward Pr (truncTime (hitTime S0) N) x = P.valueUpTo Pr N x) ∧
      ((∀ x : E, Pr x {w | hitTime S0 w = ⊤} = 0) → P.IsOptimal Pr (hitTime S0))) := by sorry

end MDPFinance.OptimalStopping

