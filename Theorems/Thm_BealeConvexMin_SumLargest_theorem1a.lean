import Mathlib
import Definitions.Def_BealeConvexMin_SumLargest_sumLargest
import Definitions.Def_BealeConvexMin_SumLargest_Forms

namespace BealeConvexMin.SumLargest

/-- Beale (1955), Theorem 1 (a), p. 179, first half. Let `A = A_0 + Σ_l A_l z_l + Σ_{f=1}^{s} φ_f u_f`,
`L_0 = c_00 + Σ_l c_0l z_l + Σ_{f=1}^{s} θ_f u_f`, `L_f = L_0 − u_f` (`f = 1, …, s`), and let `C` be
`A` plus the sum of the `τ` largest of `L_0, L_1, …, L_s`, where `τ ≤ s`. If all the `u_f` and the
`z_l` with `l ∈ F` are free and the other `z_l` are restricted to non-negative values, then `C` is
minimized when all the `z_l` and `u_f` vanish if and only if (4.5) holds. -/
theorem theorem1a {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ ≤ s) (F : Finset (Fin r)) :
    P.IsMinimizedAtZero τ F ↔ P.Cond45 τ F := by sorry

end BealeConvexMin.SumLargest

