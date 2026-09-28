import Mathlib
import Definitions.Def_DistInterpRO_Equivalence_Model

open MeasureTheory

namespace DistInterpRO.Equivalence

theorem dual_bound {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (hZm : ∀ i, MeasurableSet (Z i))
    (hbdd : ∀ i, BddBelow (f '' Z i))
    (α : Finset (Fin n) → ℝ) (hα : IsDualFeasible Z f α) :
    ∑ i, c i * ∑ S : Finset (Fin n), α S * (if i ∈ S then (1 : ℝ) else 0) ≤
      ∑ i, c i * ⨅ x : Z i, f x := by sorry

end DistInterpRO.Equivalence

