import Mathlib
import Definitions.Def_DualSSD_MeanRisk_secondQuantileR

namespace DualSSD.MeanRisk

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The expected outcome `μ_X = E X` (Ogryczak–Ruszczyński 2002, notation used throughout, e.g.
p. 62). A Bochner integral: every statement using it assumes `X` integrable. -/
noncomputable def mean (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ ω, X ω ∂P

/-- The vertical diameter of the dual dispersion space (3.6) (Ogryczak–Ruszczyński 2002, §3,
p. 66): `h_X(p) = μ_X p − F_X^(−2)(p)`, for `p ∈ [0, 1]`. -/
noncomputable def hDiam (P : Measure Ω) (X : Ω → ℝ) (p : ℝ) : ℝ :=
  mean P X * p - secondQuantileR P X p

/-- The Gini mean difference, defined as the doubled area of the dual dispersion space (3.8)
(Ogryczak–Ruszczyński 2002, §3, p. 67): `Γ_X = 2 ∫_0^1 (μ_X p − F_X^(−2)(p)) dp`. -/
noncomputable def gini (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  2 * ∫ p in (0 : ℝ)..1, (mean P X * p - secondQuantileR P X p)

/-- The tail Gini measure (4.8) (Ogryczak–Ruszczyński 2002, §4, p. 72), for `p ∈ (0, 1]`:
`G_X(p) = (2/p²) ∫_0^p (μ_X α − F_X^(−2)(α)) dα`. -/
noncomputable def tailGini (P : Measure Ω) (X : Ω → ℝ) (p : ℝ) : ℝ :=
  2 / p ^ 2 * ∫ α in (0 : ℝ)..p, (mean P X * α - secondQuantileR P X α)

/-- `Γ_X = G_X(1)` (Ogryczak–Ruszczyński 2002, §5, p. 73), by unfolding (3.8) and (4.8). -/
theorem gini_eq_tailGini_one (P : Measure Ω) (X : Ω → ℝ) : gini P X = tailGini P X 1 := by
  simp [gini, tailGini]

end DualSSD.MeanRisk
