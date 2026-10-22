import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

namespace KendallBD.MinVar

/-- Kendall (1948), (14c), p. 4: the variance of the population size in its
integral form, for the process starting from one ancestor. -/
noncomputable def fluct (lam mu : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-2 * KendallBD.Sol.rho lam mu t) *
    ∫ τ in (0 : ℝ)..t, Real.exp (KendallBD.Sol.rho lam mu τ) * (lam τ + mu τ)

/-- Continuous, nonnegative birth and death rates on nonnegative time. Continuity
is the stated regularity convention used to read Kendall's differential formulas. -/
def Admissible (lam mu : ℝ → ℝ) : Prop :=
  Continuous lam ∧ Continuous mu ∧
    ∀ t : ℝ, 0 ≤ t → 0 ≤ lam t ∧ 0 ≤ mu t

/-- Kendall (1948), (13), p. 4: the mean population size of a process with
rates `lam`, `mu`, restricted to nonnegative time. -/
def HasMean (lam mu nbar : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → Real.exp (-KendallBD.Sol.rho lam mu t) = nbar t

/-- The logarithmic derivative of the prescribed positive mean, (55), p. 11.
Statements using this definition assume `ContDiff ℝ 1 nbar` and `0 < nbar t`. -/
noncomputable def growth (nbar : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv nbar t / nbar t

/-- The nonnegative birth rate in Kendall's minimum-fluctuation choice (56), p. 12. -/
noncomputable def lamStar (nbar : ℝ → ℝ) (t : ℝ) : ℝ :=
  max (growth nbar t) 0

/-- The nonnegative death rate in Kendall's minimum-fluctuation choice (56), p. 12. -/
noncomputable def muStar (nbar : ℝ → ℝ) (t : ℝ) : ℝ :=
  max (-growth nbar t) 0

/-- Kendall's logistic mean (58), p. 12, with parameters `a = α`, `b = β`. -/
noncomputable def logisticMean (a b : ℝ) (t : ℝ) : ℝ :=
  a / (1 + (a - 1) * Real.exp (-b * t))

end KendallBD.MinVar
