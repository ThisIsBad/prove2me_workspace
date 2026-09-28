import Mathlib
import Definitions.Def_DistInterpRO_Equivalence_Model

open MeasureTheory

namespace DistInterpRO.Equivalence

theorem theorem_2_1 {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (hZm : ∀ i, MeasurableSet (Z i)) :
    (∑ i, ((c i : ℝ) : EReal) * ⨅ x ∈ Z i, ((f x : ℝ) : EReal)) =
      ⨅ μ ∈ distSet c Z, expect μ f := by sorry

end DistInterpRO.Equivalence

