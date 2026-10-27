import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Lemma 9 (p. 58; corrected: `R_1 ≥ 0`). Fix a non-surge policy `s₁` (state 1 = Lean `0`) and a
payment `w_1` integrable on it, with `Q_1 = Q_1(s₁)`, `T_1 = T_1(s₁)`, `R_1 = R_1(w_1, s₁) ≥ 0`; let
`Q̄_2`, `T̄_2` be the surge-state values at `(0, ∞)`, and `w_2(τ) = mτ + zq_{2→1}(τ)` with `m > R_1`. If
`[T_1(λ_{2→1}T̄_2 − Q̄_2) − (Q_1 + T_1λ_{2→1})] / [Q_1(λ_{2→1}T̄_2 − Q̄_2) + λ_{2→1}(Q_1 + T_1λ_{2→1})] < z/(m − R_1) < (Q̄_2T_1 + Q_1)/(Q_1(Q̄_2 − λ_{2→1}))`,
then `r(u, 2, w, {s₁, s₂}) > 0` for every `u > 0` and every open `s₂ ⊆ (0, ∞)` (so `∂/∂u R(w, σ) > 0` in
the `∝` sense of D.3.1). Moreover the lower bound is below the upper bound (the constraint set is
feasible). -/
theorem lemma_9 (P : Primitives) (hmean : FiniteMean P) (w : Fin 2 → ℝ → ℝ) (s₁ : Set ℝ)
    (hs₁ : IsAdmissible s₁) (hw0 : IntegrableOn (w 0) s₁ (P.F 0)) (m z : ℝ)
    (hw1 : w 1 = fun τ => m * τ + z * q P 1 τ)
    (hR : 0 ≤ stateRate P 0 (w 0) s₁) (hm : stateRate P 0 (w 0) s₁ < m) :
    ((Tn P 0 s₁ * (P.sw 1 * Tn P 1 (Ioi 0) - Qn P 1 (Ioi 0)) - (Qn P 0 s₁ + Tn P 0 s₁ * P.sw 1)) /
          (Qn P 0 s₁ * (P.sw 1 * Tn P 1 (Ioi 0) - Qn P 1 (Ioi 0)) +
            P.sw 1 * (Qn P 0 s₁ + Tn P 0 s₁ * P.sw 1)) <
        z / (m - stateRate P 0 (w 0) s₁) →
      z / (m - stateRate P 0 (w 0) s₁) <
        (Qn P 1 (Ioi 0) * Tn P 0 s₁ + Qn P 0 s₁) / (Qn P 0 s₁ * (Qn P 1 (Ioi 0) - P.sw 1)) →
      ∀ s₂ : Set ℝ, IsAdmissible s₂ → ∀ u : ℝ, 0 < u → 0 < rFun P w ![s₁, s₂] 1 u) ∧
    (Tn P 0 s₁ * (P.sw 1 * Tn P 1 (Ioi 0) - Qn P 1 (Ioi 0)) - (Qn P 0 s₁ + Tn P 0 s₁ * P.sw 1)) /
          (Qn P 0 s₁ * (P.sw 1 * Tn P 1 (Ioi 0) - Qn P 1 (Ioi 0)) +
            P.sw 1 * (Qn P 0 s₁ + Tn P 0 s₁ * P.sw 1)) <
      (Qn P 1 (Ioi 0) * Tn P 0 s₁ + Qn P 0 s₁) / (Qn P 0 s₁ * (Qn P 1 (Ioi 0) - P.sw 1)) := by sorry

end DriverSurge.IC

