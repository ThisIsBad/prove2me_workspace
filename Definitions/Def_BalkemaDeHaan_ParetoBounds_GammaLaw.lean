import Mathlib

namespace BalkemaDeHaan.ParetoBounds

/-- The limit law `Γ_α` of Balkema–de Haan (1974), p. 793:
`Γ_α(x) = 1 - (1 + x)^{-α}` for `x ≥ 0`, and `Γ_α(x) = 0` for `x < 0`
("All limit distributions vanish for x < 0"). The parameter `α` is meant to be positive. -/
noncomputable def GammaLaw (α x : ℝ) : ℝ :=
  if 0 ≤ x then 1 - (1 + x) ^ (-α) else 0

end BalkemaDeHaan.ParetoBounds
