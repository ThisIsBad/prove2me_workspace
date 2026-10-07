import Mathlib

namespace BalkemaDeHaan.ExpDomain

/-- The exponential residual-life limit law `Π` of the introduction. -/
noncomputable def piLaw (x : ℝ) : ℝ :=
  if x < 0 then 0 else 1 - Real.exp (-x)

/-- The standard Gumbel extreme-value distribution function `Λ`. -/
noncomputable def lambdaLaw (x : ℝ) : ℝ :=
  Real.exp (-Real.exp (-x))

end BalkemaDeHaan.ExpDomain
