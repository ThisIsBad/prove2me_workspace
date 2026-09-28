import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_IsExpConcave
import Definitions.Def_LogRegretOCO_EWOO_ewooPoint

open MeasureTheory

namespace LogRegretOCO.EWOO

/-- §3.4, first display on p. 187 (Hazan–Agarwal–Kale 2007): for `h_t(x) = exp(-α f_t(x))`,
the EWOO point satisfies
`h_t(x_t) ≥ ∫_P h_t(x) ∏_{τ=1}^{t-1} h_τ(x) dx / ∫_P ∏_{τ=1}^{t-1} h_τ(x) dx`. -/
theorem jensen_weighted_mean (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hPbdd : Bornology.IsBounded P)
    (hPne : P.Nonempty) (hPvol : volume P ≠ 0)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t)) (hcont : ∀ t, ContinuousOn (f t) P)
    (t : ℕ) (ht : 1 ≤ t) :
    (∫ x in P, Real.exp (-α * f t x) * ∏ τ ∈ Finset.Ico 1 t, Real.exp (-α * f τ x)) /
        (∫ x in P, ∏ τ ∈ Finset.Ico 1 t, Real.exp (-α * f τ x))
      ≤ Real.exp (-α * f t (ewooPoint P α f t)) := by sorry

end LogRegretOCO.EWOO

