import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Lemma 7 (p. 57). If `w_i(τ) = mτ + a` with `m, a > 0`, then for every policy `σ` (with `w_j` and `τ`
integrable on `σ_j`, `σ_i`) where `Δ_{ji} ≤ 0`, `r(u, i, w, σ)` is strictly quasi-convex in `u > 0` (its
derivative is strictly negative up to a point and strictly positive above it). -/
theorem lemma_7 (P : Primitives) (w : Fin 2 → ℝ → ℝ) (i : Fin 2) (m a : ℝ) (hm : 0 < m)
    (ha : 0 < a) (hwi : w i = fun τ => m * τ + a) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hw : ∀ k, IntegrableOn (w k) (σ k) (P.F k))
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k))
    (hΔ : stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i) ≤ 0) :
    StrictQuasiconvexIoi (rFun P w σ i) := by sorry

end DriverSurge.IC

