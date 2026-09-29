import Mathlib

namespace DualSSD.Shared

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The (right-continuous) cumulative distribution function `F_X(η) = P{X ≤ η}` of a real random
variable `X` on the probability space `(Ω, P)` (Ogryczak–Ruszczyński 2002, §2, p. 61). -/
noncomputable def distFun (P : Measure Ω) (X : Ω → ℝ) (η : ℝ) : ℝ :=
  P.real {ω | X ω ≤ η}

/-- The second performance function (2.1), `F_X^(2)(η) = ∫_{−∞}^η F_X(ξ) dξ`
(Ogryczak–Ruszczyński 2002, §2, p. 62): the area below the distribution function up to `η`,
a Lebesgue (Bochner) integral over `(−∞, η]`. It is finite whenever `E|X| < ∞`; the theorems
that use it all assume `Integrable X P`. -/
noncomputable def secondPerformance (P : Measure Ω) (X : Ω → ℝ) (η : ℝ) : ℝ :=
  ∫ ξ in Set.Iic η, distFun P X ξ

/-- The weak second-degree stochastic dominance relation (2.2) (Ogryczak–Ruszczyński 2002, §2,
p. 62): `X ⪰_SSD Y` iff `F_X^(2)(η) ≤ F_Y^(2)(η)` for all `η ∈ ℝ` (larger outcomes preferred). -/
def SSD (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∀ η : ℝ, secondPerformance P X η ≤ secondPerformance P Y η

end DualSSD.Shared
