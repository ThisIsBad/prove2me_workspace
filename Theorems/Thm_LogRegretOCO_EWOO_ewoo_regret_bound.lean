import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_IsExpConcave
import Definitions.Def_LogRegretOCO_EWOO_ewooPoint

open MeasureTheory

namespace LogRegretOCO.EWOO

/-- Theorem 7 (Hazan–Agarwal–Kale 2007, p. 186): on a nonempty, closed, bounded, convex
`P ⊆ ℝⁿ` of positive volume, with `α > 0` and every `f_t` α-exp-concave and continuous on `P`,
the points `x_t` of EXPONENTIALLY WEIGHTED ONLINE OPTIMIZATION satisfy, for every `T ≥ 1` and
every comparator `u ∈ P`,
`∑_{t=1}^T (f_t(x_t) − f_t(u)) ≤ (1/α) n (1 + log(T + 1))`. -/
theorem ewoo_regret_bound (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hPbdd : Bornology.IsBounded P)
    (hPne : P.Nonempty) (hPvol : volume P ≠ 0)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t)) (hcont : ∀ t, ContinuousOn (f t) P)
    (T : ℕ) (hT : 1 ≤ T) (u : EuclideanSpace ℝ (Fin n)) (hu : u ∈ P) :
    ∑ t ∈ Finset.Icc 1 T, (f t (ewooPoint P α f t) - f t u)
      ≤ 1 / α * n * (1 + Real.log ((T : ℝ) + 1)) := by sorry

end LogRegretOCO.EWOO

