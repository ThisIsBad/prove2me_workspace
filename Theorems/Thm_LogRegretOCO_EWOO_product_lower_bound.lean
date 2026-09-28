import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_IsExpConcave
import Definitions.Def_LogRegretOCO_EWOO_ewooPoint
import Definitions.Def_LogRegretOCO_EWOO_shrunkSet

open MeasureTheory

namespace LogRegretOCO.EWOO

/-- §3.4, last display on p. 187 (Hazan–Agarwal–Kale 2007): for every comparator `x* ∈ P`,
`∏_{τ=1}^T h_τ(x_τ) ≥ vol(S)/vol(P) · (1/e) ∏_{τ=1}^T h_τ(x*) ≥ 1/(e(T+1)^n) ∏_{τ=1}^T h_τ(x*)`,
where `h_τ = exp(-α f_τ)`, `x_τ` is the EWOO point and `S` the shrunken set around `x*`. -/
theorem product_lower_bound (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hPbdd : Bornology.IsBounded P)
    (hPne : P.Nonempty) (hPvol : volume P ≠ 0)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t)) (hcont : ∀ t, ContinuousOn (f t) P)
    (T : ℕ) (hT : 1 ≤ T) (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ P) :
    (volume (shrunkSet P xstar T)).toReal / (volume P).toReal * (1 / Real.exp 1) *
          ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)
        ≤ ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ (ewooPoint P α f τ)) ∧
      1 / (Real.exp 1 * ((T : ℝ) + 1) ^ n) * ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)
        ≤ (volume (shrunkSet P xstar T)).toReal / (volume P).toReal * (1 / Real.exp 1) *
          ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar) := by sorry

end LogRegretOCO.EWOO

