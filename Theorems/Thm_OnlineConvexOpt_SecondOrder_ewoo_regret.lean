import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_EWOO
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open MeasureTheory OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.SecondOrder

/-- Theorem 4.4 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 61, PDF p. 83). The Exponentially Weighted Online Optimizer (Algorithm
11) run with parameter `α > 0` on `α`-exp-concave cost functions `f` over a bounded, measurable,
convex, `d`-dimensional (`d = n`) decision set `K` of positive volume guarantees, for every
`T ≥ 1`, `Regret_T(EWOO) ≤ (d/α) log T + 2/α`, using
`OnlineConvexOpt.FirstOrder.RegretT` (Eq. (1.2)) for the regret against the same cost functions.
-/
theorem ewoo_regret (n : ℕ) (hn : 0 < n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKconv : Convex ℝ K) (hKne : K.Nonempty) (hKbdd : Bornology.IsBounded K)
    (hKmeas : MeasurableSet K) (hKvol : 0 < volume K)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hEWOO : IsEWOO K α f x)
    (T : ℕ) (hT : 1 ≤ T) :
    RegretT K f x T ≤ (n / α) * Real.log T + 2 / α := by sorry

end OnlineConvexOpt.SecondOrder

