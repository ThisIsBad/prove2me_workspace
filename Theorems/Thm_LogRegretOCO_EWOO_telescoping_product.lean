import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_IsExpConcave
import Definitions.Def_LogRegretOCO_EWOO_ewooPoint

open MeasureTheory

namespace LogRegretOCO.EWOO

/-- Eq. (18) (Hazan–Agarwal–Kale 2007, p. 187): for every `t ≥ 1`,
`∏_{τ=1}^t h_τ(x_τ) ≥ ∫_P ∏_{τ=1}^t h_τ(x) dx / ∫_P 1 dx`, and `∫_P 1 dx = vol(P)`,
where `h_τ(x) = exp(-α f_τ(x))` and `x_τ` is the EWOO point. -/
theorem telescoping_product (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hPbdd : Bornology.IsBounded P)
    (hPne : P.Nonempty) (hPvol : volume P ≠ 0)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t)) (hcont : ∀ t, ContinuousOn (f t) P)
    (t : ℕ) (ht : 1 ≤ t) :
    (∫ x in P, ∏ τ ∈ Finset.Icc 1 t, Real.exp (-α * f τ x)) / (∫ _x in P, (1 : ℝ))
        ≤ ∏ τ ∈ Finset.Icc 1 t, Real.exp (-α * f τ (ewooPoint P α f τ)) ∧
      (∫ _x in P, (1 : ℝ)) = (volume P).toReal := by sorry

end LogRegretOCO.EWOO

