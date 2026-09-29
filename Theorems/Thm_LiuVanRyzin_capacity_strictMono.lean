import Mathlib
import Definitions.Def_LiuVanRyzin_PowerModel

namespace LiuVanRyzin

/-- Proposition 5 (Liu–van Ryzin 2008, p. 1123). Under the uniform law on `[0, Ū]` and the
power utility `x ^ γ`, on `p₁ ≤ v ≤ Ū` the capacity `C(v)` is strictly increasing in the cutoff
`v`, and so is the fill rate `q(v)`; hence `C` is strictly increasing in `q` as well. -/
theorem capacity_strictMono (N Ubar p₁ p₂ γ : ℝ) (hN : 0 < N) (hU : 0 < Ubar)
    (hp : p₂ < p₁) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictMonoOn (capacity N Ubar p₁ p₂ γ) (Set.Icc p₁ Ubar) ∧
      StrictMonoOn (fillRate p₁ p₂ γ) (Set.Icc p₁ Ubar) := by sorry

end LiuVanRyzin
