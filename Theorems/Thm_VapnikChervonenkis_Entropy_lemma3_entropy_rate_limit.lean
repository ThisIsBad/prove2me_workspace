import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Entropy_entropy

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- **Lemma 3** of Vapnik and Chervonenkis (1971), p. 273: the sequence `H^S(l)/l` has a limit
`c` with `0 ≤ c ≤ 1` as `l → ∞`. `hΔ` is the paper's assumption (p. 273) that the index is a
measurable function of the sample. -/
theorem lemma3_entropy_rate_limit {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧
      Tendsto (fun l : ℕ => entropy S P l / (l : ℝ)) atTop (𝓝 c) := by sorry

end VapnikChervonenkis.Entropy
