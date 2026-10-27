import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Remark 2 (p. 57). Let `σ` be a policy with `τ` integrable on `σ_1`, `σ_2` and `w_j` integrable on
`σ_j`, and let `w_i(u) = mu + zq_{i→j}(u)`. Then `W_i = m(T_i − 1) + z(Q_i − λ_{i→j})`, and for `u > 0`
`u T_iT_j · r(u, i, w, σ) = q_{i→j}(u)[(R_j − m)T_jT_i + mT_j + zQ_jT_i + zT_jλ_{i→j}] + u[Q_iT_j(m − R_j) + Q_j(m − zQ_i + zλ_{i→j})]`,
so `∂/∂u R(w, σ)` (which has the sign of `r`) has the sign of the right-hand side. -/
theorem remark_2 (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k)) (i : Fin 2)
    (hwj : IntegrableOn (w (other i)) (σ (other i)) (P.F (other i))) (m z : ℝ)
    (hwi : w i = fun u => m * u + z * q P i u) :
    Wn P i (w i) (σ i) = m * (Tn P i (σ i) - 1) + z * (Qn P i (σ i) - P.sw i) ∧
    ∀ u : ℝ, 0 < u →
      u * Tn P i (σ i) * Tn P (other i) (σ (other i)) * rFun P w σ i u =
          q P i u * ((stateRate P (other i) (w (other i)) (σ (other i)) - m) *
                Tn P (other i) (σ (other i)) * Tn P i (σ i) + m * Tn P (other i) (σ (other i)) +
              z * Qn P (other i) (σ (other i)) * Tn P i (σ i) +
              z * Tn P (other i) (σ (other i)) * P.sw i) +
            u * (Qn P i (σ i) * Tn P (other i) (σ (other i)) *
                (m - stateRate P (other i) (w (other i)) (σ (other i))) +
              Qn P (other i) (σ (other i)) * (m - z * Qn P i (σ i) + z * P.sw i)) ∧
      SignType.sign (rFun P w σ i u) =
        SignType.sign (q P i u * ((stateRate P (other i) (w (other i)) (σ (other i)) - m) *
                Tn P (other i) (σ (other i)) * Tn P i (σ i) + m * Tn P (other i) (σ (other i)) +
              z * Qn P (other i) (σ (other i)) * Tn P i (σ i) +
              z * Tn P (other i) (σ (other i)) * P.sw i) +
            u * (Qn P i (σ i) * Tn P (other i) (σ (other i)) *
                (m - stateRate P (other i) (w (other i)) (σ (other i))) +
              Qn P (other i) (σ (other i)) * (m - z * Qn P i (σ i) + z * P.sw i))) := by sorry

end DriverSurge.IC

