import Mathlib
import Definitions.Def_ServiceParts_Shortfall_ShortfallModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ServiceParts.Shortfall

/-- Section 8.1.1, p. 184 (and Section 8.1.2, p. 185, `V_0 = 0`). Since `E[D] < c` and the demands
are i.i.d., the shortfall process has a stationary distribution, the law of
`V = sup_{n ≥ 0} ∑_{k=1}^{n} (D_k − c)`:
1. `V` is finite almost surely;
2. for every `v`, `P{V_n > v} → P{V > v}` as `n → ∞`, where `V_n` is the shortfall process
   started from `V_0 = 0`;
3. the law of `V` is stationary for (8.1): if `D` is a demand independent of `V`, then
   `[V + D − c]^+` has the law of `V`. -/
theorem stationary_shortfall_exists {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) :
    P {ω | M.walkMax ω = ⊤} = 0 ∧
    (∀ v : ℝ, Tendsto (fun n : ℕ => P {ω | v < M.shortfall n ω}) atTop
        (𝓝 (P {ω | v < M.stationaryShortfall ω}))) ∧
    (∀ v : ℝ, P {ω | v < M.stationaryShortfall ω} =
        ∫⁻ ω, (P.map (M.demand 1))
          {d : ℝ | v < max (M.stationaryShortfall ω + d - M.capacity) 0} ∂P) := by sorry

end ServiceParts.Shortfall

