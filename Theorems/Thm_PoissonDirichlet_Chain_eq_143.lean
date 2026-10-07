import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain
/-- (143), p. 888, 0-based: under `PD(α, θ)` (`0 < α < 1`, `θ > -α`), with `L = lim n V_n^α`
the local time (24), `L = Y_1^α lim_{n → ∞} n (R_1 ⋯ R_n)^α` almost surely. Here
`Yseq (V ω) 0` is `Y_1` and `∏_{i < k+1} PoissonDirichlet.Ratio.ratio (V ω) i` is `R_1 ⋯ R_{k+1}`. -/
theorem eq_143 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α θ P V)
    (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V ω k ^ α) atTop (𝓝 (L ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => Yseq (V ω) 0 ^ α *
        (((k : ℝ) + 1) * (∏ i ∈ Finset.range (k + 1), PoissonDirichlet.Ratio.ratio (V ω) i) ^ α)) atTop (𝓝 (L ω)) := by sorry

end PoissonDirichlet.Chain

