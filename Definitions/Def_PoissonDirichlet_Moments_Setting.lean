import Mathlib
import Definitions.Def_PoissonDirichlet_Ratio_Setting
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Moments

/-- (27), last expression, 0-based: `Xseq α l v k = l · (v k)^{-α}` is `X_{k+1} = L V_{k+1}^{-α}`
when `l` is the local time `L` of (24). -/
noncomputable def Xseq (α l : ℝ) (v : ℕ → ℝ) (k : ℕ) : ℝ := l * v k ^ (-α)

/-- (43), second expression: `C_{α,θ} = Γ(θ + 1) / Γ(θ/α + 1) · Γ(1 - α)^{θ/α}`. -/
noncomputable def pdConst (α θ : ℝ) : ℝ :=
  Real.Gamma (θ + 1) / Real.Gamma (θ / α + 1) * Real.Gamma (1 - α) ^ (θ / α)

/-- Corollary 18: `E(t) = ∫_t^∞ x^{-1} e^{-x} dx` (used for `t > 0`). -/
noncomputable def expIntE (t : ℝ) : ℝ :=
  ∫ x in Set.Ioi t, x⁻¹ * Real.exp (-x)

end PoissonDirichlet.Moments
