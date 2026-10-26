import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory Filter Topology

/-- Proof of Proposition 3.1, Existence (pp. 32–34): under the window condition of the
non-degenerate case, for every càdlàg input `x` the successive approximations (A.3),
`u_0 = 0`, `u_{n+1} = x + Ψ^a_B(u_n)`, converge uniformly on every `[0, T]` to a càdlàg
path `u⋆`, and `u⋆` solves (3.1). -/
theorem existence (μ : Measure ℝ) [IsProbabilityMeasure μ] (a δ ε : ℝ)
    (hδ : 0 < δ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hB₀ : μ (Set.Icc 0 δ) < ENNReal.ofReal ε)
    (hB : ∀ y, 0 ≤ y → μ (Set.Ioc y (y + δ)) < ENNReal.ofReal ε)
    (x : ℝ → ℝ) (hx : IsCadlag x) :
    ∃ uStar : ℝ → ℝ, IsCadlag uStar ∧
      (∀ T, 0 ≤ T → Tendsto (fun n => supNorm T (picard μ a x n - uStar)) atTop (𝓝 0)) ∧
      SolvesRegulator μ a x uStar := by sorry

end ReedGGN.Regulator

