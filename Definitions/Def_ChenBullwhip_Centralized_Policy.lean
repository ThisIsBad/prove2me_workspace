import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand

open MeasureTheory ProbabilityTheory

namespace ChenBullwhip.Centralized

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- p. 437, the display before Eq. (3): the moving-average estimate of the mean lead-time demand,
`D̂ᴸₜ = L (∑_{i=1}^p D_{t-i}) / p`. -/
noncomputable def AR1Demand.Dhat (X : AR1Demand P) (L p : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  (L : ℝ) * ((∑ i ∈ Finset.Icc 1 p, X.D (t - i) ω) / p)

/-- p. 437, below Eq. (3): the one-period forecast error `eₜ = Dₜ - D̂¹ₜ`. -/
noncomputable def AR1Demand.err (X : AR1Demand P) (p : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  X.D t ω - X.Dhat 1 p t ω

/-- p. 437, Eq. (3): `σ̂ᴸₑₜ = C_{L,ρ} √(∑_{i=1}^p (e_{t-i})² / p)`. The paper leaves the constant
`C_{L,ρ}` unspecified ("a constant function of `L`, `ρ` and `p`"); it is the free real `C`. -/
noncomputable def AR1Demand.sigmaHat (X : AR1Demand P) (C : ℝ) (p : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  C * Real.sqrt ((∑ i ∈ Finset.Icc 1 p, (X.err p (t - i) ω) ^ 2) / p)

/-- p. 437, Eq. (2): the order-up-to point `yₜ = D̂ᴸₜ + z σ̂ᴸₑₜ`. -/
noncomputable def AR1Demand.orderUpTo (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (t : ℤ) (ω : Ω) :
    ℝ :=
  X.Dhat L p t ω + z * X.sigmaHat C p t ω

/-- p. 437, §2.2: the (signed) order `qₜ = yₜ - y_{t-1} + D_{t-1}`. -/
noncomputable def AR1Demand.order (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  X.orderUpTo C z L p t ω - X.orderUpTo C z L p (t - 1) ω + X.D (t - 1) ω

end ChenBullwhip.Centralized
