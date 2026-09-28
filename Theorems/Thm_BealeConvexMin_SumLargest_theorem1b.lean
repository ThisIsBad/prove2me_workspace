import Mathlib
import Definitions.Def_BealeConvexMin_SumLargest_sumLargest
import Definitions.Def_BealeConvexMin_SumLargest_Forms

namespace BealeConvexMin.SumLargest

/-- Beale (1955), Theorem 1 (b), p. 180. In the setting of Theorem 1 (a) but with `τ = s + 1`
(so `C = A + L_0 + L_1 + ⋯ + L_s`), `C` is minimized when all the `z_l` and `u_f` vanish if and
only if (4.5) holds and in addition `φ_f + τθ_f − 1 = 0` for all `f`. Otherwise (for an `f` with
`φ_f + τθ_f − 1 ≠ 0`) `C` can be decreased by giving `u_f` some value with the opposite sign to
this quantity, the other variables staying at zero. `F` is the set of `l` with `z_l` free. -/
theorem theorem1b {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ = s + 1) (F : Finset (Fin r)) :
    (P.IsMinimizedAtZero τ F ↔
      P.Cond45 τ F ∧ ∀ f : Fin s, P.φ f + (τ : ℝ) * P.θ f - 1 = 0) ∧
    (∀ f : Fin s, P.φ f + (τ : ℝ) * P.θ f - 1 ≠ 0 →
      ∃ v : ℝ, v * (P.φ f + (τ : ℝ) * P.θ f - 1) < 0 ∧
        P.C τ 0 (Pi.single f v) < P.C τ 0 0) := by sorry

end BealeConvexMin.SumLargest

