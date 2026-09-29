import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Entropy_entropy

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- Vapnik and Chervonenkis (1971), p. 273, Subsection 6: "Inequality (13) implies that
`H^S(l_1 + l_2) ≤ H^S(l_1) + H^S(l_2)`." The entropy `H^S(l) = E log₂ Δ^S(x_1, …, x_l)` is
subadditive in the sample size. `hΔ` is the paper's assumption (p. 273) that the index is a
measurable function of the sample. -/
theorem entropy_subadditive {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) (l₁ l₂ : ℕ) :
    entropy S P (l₁ + l₂) ≤ entropy S P l₁ + entropy S P l₂ := by sorry

end VapnikChervonenkis.Entropy
