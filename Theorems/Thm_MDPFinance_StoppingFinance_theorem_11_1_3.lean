import Mathlib
import Definitions.Def_MDPFinance_StoppingFinance_BinomialModel

open MeasureTheory Filter Topology

namespace MDPFinance.StoppingFinance

/-- **Theorem 11.1.3** (pp. 337-338), the perpetual American put `P(x) := sup_{τ ≤ ∞}
𝔼^ℚ_x[β^τ (K − S_τ)]` (reward `0` on `{τ = ∞}`). a) `P(x) = J(x) = lim_n J_n(x)` for `x ∈ E`.
b) `P = 𝒯P` and `0 ≤ P ≤ K` on `E`. c) `P` is the smallest superharmonic majorant of `(K−x)⁺`.
d) With `E^* := {x ∈ E | P(x) = (K−x)⁺}` and `J_{f^*} := lim_n 𝒯_{f^*}^n 0`: if `J_{f^*} ≥ 𝒯J_{f^*}`
then `P = J_{f^*}` on `E` and `τ^* := inf{n | X_n ∈ E^*}` is an optimal exercise time. e) There is
`x^* ∈ [0,K]` with `E^* = {x ∈ E | x ≤ x^*}`. -/
theorem theorem_11_1_3 (M : BinomialModel) (Q : Measure (ℕ → Bool)) (hQ : M.IsPathLaw Q) :
    (∀ x ∈ M.E, M.perpetualValue Q x = (M.Jlim x : EReal) ∧
      Tendsto (fun n => M.J n x) atTop (𝓝 (M.Jlim x))) ∧
    ((∀ x ∈ M.E, M.Jlim x = M.T M.Jlim x) ∧ ∀ x ∈ M.E, 0 ≤ M.Jlim x ∧ M.Jlim x ≤ M.K) ∧
    (M.Superharmonic M.Jlim ∧ (∀ x ∈ M.E, M.payoff x ≤ M.Jlim x) ∧
      ∀ V : ℝ → ℝ, M.Superharmonic V → (∀ x ∈ M.E, M.payoff x ≤ V x) →
        ∀ x ∈ M.E, M.Jlim x ≤ V x) ∧
    ((∀ x ∈ M.E, M.T (M.JfStar {y | y ∈ M.E ∧ M.Jlim y = M.payoff y}) x ≤
        M.JfStar {y | y ∈ M.E ∧ M.Jlim y = M.payoff y} x) →
      ∀ x ∈ M.E, M.Jlim x = M.JfStar {y | y ∈ M.E ∧ M.Jlim y = M.payoff y} x ∧
        IsStoppingTime (M.exerciseTime x {y | y ∈ M.E ∧ M.Jlim y = M.payoff y}) ∧
        M.EReward Q x (M.exerciseTime x {y | y ∈ M.E ∧ M.Jlim y = M.payoff y}) =
          M.perpetualValue Q x) ∧
    (∃ xstar : ℝ, 0 ≤ xstar ∧ xstar ≤ M.K ∧
      {y | y ∈ M.E ∧ M.Jlim y = M.payoff y} = {y | y ∈ M.E ∧ y ≤ xstar}) := by sorry

end MDPFinance.StoppingFinance
