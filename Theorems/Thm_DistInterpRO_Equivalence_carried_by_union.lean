import Mathlib
import Definitions.Def_DistInterpRO_Equivalence_Model

open MeasureTheory

namespace DistInterpRO.Equivalence

theorem carried_by_union {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (hZm : ∀ i, MeasurableSet (Z i))
    (μ : Measure (Fin m → ℝ)) (hμ : μ ∈ distSet c Z) :
    μ (⋃ i, Z i)ᶜ = 0 ∧ expect μ f = expect (μ.restrict (⋃ i, Z i)) f := by sorry

end DistInterpRO.Equivalence

