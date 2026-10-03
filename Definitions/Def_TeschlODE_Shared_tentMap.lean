import Mathlib

namespace TeschlODE.Shared

/-- Teschl, §11.3–11.4, p. 297, (11.12) and p. 298, (11.15): the tent map
`T_µ(x) = (µ/2)(1 − |2x − 1|)`, considered as a map on `M = ℝ` (for `µ > 2` it no longer maps
`[0, 1]` into itself). The parameter `µ` is unrestricted here; theorems assume `µ ≥ 2` or
`µ > 2` as the book does. -/
noncomputable def tentMap (μ : ℝ) (x : ℝ) : ℝ :=
  μ / 2 * (1 - |2 * x - 1|)

end TeschlODE.Shared
