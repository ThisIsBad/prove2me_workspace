import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Lemma 10 (p. 58). Fix a surge policy `s₂` (state 2 = Lean `1`) and a payment `w_2` integrable on it,
with `Q_2 = Q_2(s₂)`, `T_2 = T_2(s₂)` and `R_2 = R_2(w_2, s₂) > 0`; let `Q̄_1`, `T̄_1` be the non-surge
values at `(0, ∞)`, and `w_1(τ) = mτ + zq_{1→2}(τ)` with `m = R_2`. If
`−(T_2λ_{1→2} + Q_2) / [Q_2(λ_{1→2}T̄_1 − Q̄_1) + λ_{1→2}(T_2λ_{1→2} + Q_2)] < z/R_2 < 1/(Q̄_1 − λ_{1→2})`,
then `r(u, 1, w, {s₁, s₂}) > 0` for every `u > 0` and every open `s₁ ⊆ (0, ∞)` (so `∂/∂u R(w, σ) > 0` in
the `∝` sense of D.3.1). Moreover the lower bound is below the upper bound (the constraint set is
feasible). -/
theorem lemma_10 (P : Primitives) (hmean : FiniteMean P) (w : Fin 2 → ℝ → ℝ) (s₂ : Set ℝ)
    (hs₂ : IsAdmissible s₂) (hw1 : IntegrableOn (w 1) s₂ (P.F 1)) (z : ℝ)
    (hR : 0 < stateRate P 1 (w 1) s₂)
    (hw0 : w 0 = fun τ => stateRate P 1 (w 1) s₂ * τ + z * q P 0 τ) :
    (-(Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂) /
          (Qn P 1 s₂ * (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) +
            P.sw 0 * (Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂)) <
        z / stateRate P 1 (w 1) s₂ →
      z / stateRate P 1 (w 1) s₂ < 1 / (Qn P 0 (Ioi 0) - P.sw 0) →
      ∀ s₁ : Set ℝ, IsAdmissible s₁ → ∀ u : ℝ, 0 < u → 0 < rFun P w ![s₁, s₂] 0 u) ∧
    -(Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂) /
          (Qn P 1 s₂ * (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) +
            P.sw 0 * (Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂)) <
      1 / (Qn P 0 (Ioi 0) - P.sw 0) := by sorry

end DriverSurge.IC

