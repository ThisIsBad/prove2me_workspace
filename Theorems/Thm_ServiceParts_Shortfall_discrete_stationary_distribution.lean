import Mathlib
import Definitions.Def_ServiceParts_Shortfall_DiscreteShortfallModel

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Shortfall

/-- Section 8.1.2, p. 186. Since `E[D] < c`, the shortfall chain started from `V_0 = 0` has a
steady-state distribution `π_i = lim_{n → ∞} P{V_n = i}`, and `π` solves
`π𝒫 = π`, `∑ π_i = 1`, `π_i ≥ 0`, where `𝒫 = [p_{ij}]` is the transition matrix of p. 185. -/
theorem discrete_stationary_distribution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : DiscreteShortfallModel Ω P) :
    ∃ π : ℕ → ℝ,
      (∀ i, Tendsto (fun n : ℕ => (P {ω | M.shortfall n ω = i}).toReal) atTop (𝓝 (π i))) ∧
      (∀ j, HasSum (fun i => π i * M.transProb i j) (π j)) ∧
      HasSum π 1 ∧
      (∀ i, 0 ≤ π i) := by sorry

end ServiceParts.Shortfall

