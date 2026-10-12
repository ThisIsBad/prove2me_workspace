import Mathlib

open MeasureTheory

namespace BoundedNV.Pooling

/-- Equation (2): the logit choice density on the decision domain `S`. -/
noncomputable def logitDensity (S : Set ℝ) (u : ℝ → ℝ) (β : ℝ) (y : ℝ) : ℝ :=
  S.indicator (fun y => Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) y

/-- The choice distribution associated with the logit density, p. 571. -/
noncomputable def logitCDF (S : Set ℝ) (u : ℝ → ℝ) (β : ℝ) (y : ℝ) : ℝ :=
  ∫ v in Set.Iic y, logitDensity S u β v

/-- Expectation of `g` under the logit choice distribution. -/
noncomputable def logitExp (S : Set ℝ) (u : ℝ → ℝ) (β : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ y, g y * logitDensity S u β y

end BoundedNV.Pooling
