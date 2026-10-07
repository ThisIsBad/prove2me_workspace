import Mathlib
import Definitions.Def_PoissonDirichlet_Moments_Setting
import Definitions.Def_PoissonDirichlet_Ratio_Setting
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain

/-- (45), 0-based: `Yseq v k = v k / (v k + v (k+1) + ⋯)` is `Y_{k+1} = V_{k+1} / (V_{k+1} +
V_{k+2} + ⋯)`. -/
noncomputable def Yseq (v : ℕ → ℝ) (k : ℕ) : ℝ := v k / ∑' j, v (k + j)

/-- (125), first expression, 0-based: `YofR r k = (1 + r k + r k r (k+1) + ⋯)⁻¹` is
`Y_{k+1} = (1 + R_{k+1} + R_{k+1} R_{k+2} + ⋯)^{-1}` as a function of the ratios
`R_1, R_2, …` (`r i` plays the role of `R_{i+1}`). -/
noncomputable def YofR (r : ℕ → ℝ) (k : ℕ) : ℝ :=
  (1 + ∑' j, ∏ i ∈ Finset.range (j + 1), r (k + i))⁻¹

/-- `Σ_1 = R_1 + R_1 R_2 + R_1 R_2 R_3 + ⋯` as a function of the ratios; by (32) this is
`(1 - V_1) / V_1`. -/
noncomputable def SigofR (r : ℕ → ℝ) : ℝ := ∑' j, ∏ i ∈ Finset.range (j + 1), r i

/-- `IsStarLaw α θ μ` (Theorem 38, the law `P*_{α,θ}`): under the probability measure `μ` on
sequences `r`, the coordinates `r 0, r 1, …` (the `R_1, R_2, …`) are independent and `r k`
(that is `R_{k+1}`) has law `beta(θ + (k+1) α, 1)`. -/
def IsStarLaw (α θ : ℝ) (μ : Measure (ℕ → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ iIndepFun (fun k (r : ℕ → ℝ) => r k) μ ∧
    ∀ k : ℕ, HasLaw (fun r : ℕ → ℝ => r k) (betaMeasure (θ + ((k : ℝ) + 1) * α) 1) μ

/-- (138): `K_{α,θ} = Γ(θ + 1) Γ(1 - α)^{θ/α}` (for `0 < α < 1`, `θ > -α`). -/
noncomputable def chainConst (α θ : ℝ) : ℝ :=
  Real.Gamma (θ + 1) * Real.Gamma (1 - α) ^ (θ / α)

/-- The forward transition density of Theorem 38 (ii), (139), from `Y_n = y` to
`Y_{n+1} = z`, with `n = k + 1`, written with the factor `α` that (139) as printed omits (it is
forced by Bayes' rule from (128), (146) and the beta(θ + nα, 1) density, and it is the factor
`α^{n-1}` of Corollary 41):
`α y^{-α-1} (1 - y)^{nα+θ-1} r(α, θ + nα, z) / r(α, θ + nα - α, y)` for `0 < y < 1`,
`0 < z < y/(1 - y)`, and `0` otherwise. Here `rf θ' y` plays the role of `r(α, θ', y)` (140). -/
noncomputable def transDens (α θ : ℝ) (rf : ℝ → ℝ → ℝ) (k : ℕ) (y z : ℝ) : ℝ :=
  if 0 < y ∧ y < 1 ∧ 0 < z ∧ z < y / (1 - y) then
    α * y ^ (-α - 1) * (1 - y) ^ (((k : ℝ) + 1) * α + θ - 1) *
      rf (θ + ((k : ℝ) + 1) * α) z / rf (θ + (k : ℝ) * α) y
  else 0

/-- The `m`-fold additive convolution power of a measure on `ℝ`: `convPow ν 0 = δ_0`,
`convPow ν (m+1) = convPow ν m ∗ ν`. -/
noncomputable def convPow (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | m + 1 => (convPow ν m).conv ν

end PoissonDirichlet.Chain
