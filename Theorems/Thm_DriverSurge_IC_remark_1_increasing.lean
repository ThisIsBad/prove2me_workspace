import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Remark 1, bullet 4 (p. 57; corrected: the sign change of `r` is at some `U ∈ [0, ∞]`, not
`U ∈ (0, ∞]`). For a policy `σ` with `w_k` and `τ` integrable on `σ_k`: if `Δ_{ji} < 0` and `w_i(u)/u` is
non-decreasing on `(0, ∞)`, then `r(u, i, w, σ)` is strictly increasing in `u > 0`, and it is negative
below some `U ∈ [0, ∞]` and positive above it. -/
theorem remark_1_increasing (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ)
    (hσ : IsPolicy σ) (hw : ∀ k, IntegrableOn (w k) (σ k) (P.F k))
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k)) (i : Fin 2)
    (hΔ : stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i) < 0)
    (hmono : MonotoneOn (fun u : ℝ => w i u / u) (Ioi 0)) :
    StrictMonoOn (rFun P w σ i) (Ioi 0) ∧
    ∃ U : EReal, 0 ≤ U ∧
      (∀ u : ℝ, 0 < u → (u : EReal) < U → rFun P w σ i u < 0) ∧
      (∀ u : ℝ, 0 < u → U < (u : EReal) → 0 < rFun P w σ i u) := by sorry

end DriverSurge.IC

