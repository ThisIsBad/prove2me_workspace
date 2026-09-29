import Mathlib
import Definitions.Def_PathFindingLP_Centering_SlackSensitivity

open Matrix

namespace PathFindingLP.Centering

/-- Lemma 3 (Split Newton Step), §IV.B, p. 428: for feasible `(x_old, w_old)` and `r ≥ 0`, put
`x_new = x_old - (1/(1+r)) h_t(x_old, w_old)` and
`w_new = w_old + (r/(1+r)) W_old S_old⁻¹ A h_t(x_old, w_old)`. If
`δ_t(x_old, w_old) ≤ 1 / (8 γ(s(x_old), w_old))` then `(x_new, w_new)` is feasible and
`δ_t(x_new, w_new) ≤ (2/(1+r)) γ(s(x_old), w_old) δ_t(x_old, w_old)²`. -/
theorem split_newton_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n) (t r : ℝ) (hr : 0 ≤ r)
    (xOld : Fin n → ℝ) (wOld : Fin m → ℝ) (hfeas : IsFeasible A b xOld wOld)
    (hδ : centrality A b c t xOld wOld ≤
      1 / (8 * slackSensitivity A (slack A b xOld) wOld)) :
    let h := newtonStep A b c t xOld wOld
    let xNew := xOld - (1 / (1 + r)) • h
    let wNew := wOld + (r / (1 + r)) •
      ((diagonal wOld * diagonal (fun i => (slack A b xOld i)⁻¹) * A) *ᵥ h)
    IsFeasible A b xNew wNew ∧
      centrality A b c t xNew wNew ≤
        2 / (1 + r) * slackSensitivity A (slack A b xOld) wOld *
          centrality A b c t xOld wOld ^ 2 := by sorry

end PathFindingLP.Centering

