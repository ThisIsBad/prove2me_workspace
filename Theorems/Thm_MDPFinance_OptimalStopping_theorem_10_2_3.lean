import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.2.3** (p. 313), under (B). a) `d := lim_n d_n` exists; with `S^* := {d ≥ 0}`,
`S^* = ∩_n S_n^* = {J = g}` and `f^* := 1_{S^*}` is a maximizer of `J`. b) If `G_{f^*} ≥ T G_{f^*}`
and `ℙ_x(τ_{f^*} < ∞) = 1` for all `x`, then `τ^* := inf{n | X_n ∈ S^*}` is an optimal stopping
time and `G_{f^*}(x) = 𝔼_x[R_{τ^*}] = V_∞^*(x)`. -/
theorem theorem_10_2_3 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr) :
    (∃ d : E → EReal,
      (∀ x : E, Tendsto (fun n => P.d n x) atTop (𝓝 (d x))) ∧
      ({x : E | 0 ≤ d x} = ⋂ n : ℕ, P.stopSet n) ∧
      ({x : E | 0 ≤ d x} = {x : E | P.Jlim x = (P.g x : EReal)}) ∧
      P.IsMaximizer {x : E | 0 ≤ d x} P.Jlim) ∧
    ((∀ x : E, P.T (P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)}) x ≤
        P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x) →
      (∀ x : E, Pr x {w | P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)} w = ⊤} = 0) →
      P.IsOptimal Pr (P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)}) ∧
        ∀ x : E, P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x =
          P.EReward Pr (P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)}) x) := by sorry

end MDPFinance.OptimalStopping

