import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology

namespace MDPFinance.OptimalStopping

/-- **Corollary 10.2.6** (p. 314), under (B), for a maximizer `f^* = 1_S` of `J`. a) If the
Markov Decision Model has a bounding function `b` with `βα_b < 1`, then `G_{f^*} = J`; if moreover
`ℙ_x(τ_{f^*} < ∞) = 1` for all `x`, `τ_{f^*}` is optimal. b) If `sup c < 0`, `β = 1` and
`G_{f^*} = J`, then `ℙ_x(τ_{f^*} < ∞) = 1` for all `x` and `τ_{f^*}` is optimal. c) If `J − g` is
bounded above and `ℙ_x(τ_{f^*} < ∞) = 1` for all `x`, then `τ_{f^*}` is optimal and
`G_{f^*} = J`. -/
theorem corollary_10_2_6 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr)
    (S : Set E) (hS : P.IsMaximizer S P.Jlim) :
    (∀ B : P.BoundingFunction, P.beta * B.alpha < 1 →
      (∀ x : E, P.Gf Pr S x = P.Jlim x) ∧
      ((∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) → P.IsOptimal Pr (P.ruleTime S))) ∧
    ((∃ s : ℝ, s < 0 ∧ ∀ x : E, P.c x ≤ s) → P.beta = 1 → (∀ x : E, P.Gf Pr S x = P.Jlim x) →
      (∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) ∧ P.IsOptimal Pr (P.ruleTime S)) ∧
    ((∃ C : ℝ, ∀ x : E, P.Jlim x ≤ (P.g x : EReal) + (C : EReal)) →
      (∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) →
      P.IsOptimal Pr (P.ruleTime S) ∧ ∀ x : E, P.Gf Pr S x = P.Jlim x) := by sorry

end MDPFinance.OptimalStopping

