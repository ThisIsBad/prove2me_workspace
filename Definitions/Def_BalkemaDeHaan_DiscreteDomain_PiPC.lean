import Mathlib

namespace BalkemaDeHaan.DiscreteDomain

/-- The discrete residual-life limit law `Π_{p,c}` of the introduction (p. 793, PDF 2), for
`p > 0` and `c ≥ 0`; `[·]` is the integer part (`Int.floor`).
* For `c > 0`: `Π_{p,c}(x) = Γ_{p,(pc)⁻¹}(cx) = 1 - exp(-p [1 + log(1 + cx)/(cp)])` for `x ≥ 0`.
* For `c = 0`: `Π_{p,0}(x) = Π_p(x/p) = 1 - exp(-p [1 + x/p])` for `x ≥ 0`.
* Every case is `0` for `x < 0` ("All limit distributions vanish for `x < 0`").
The case split keeps `c = 0` from being the junk value of `log(1 + 0·x)/(0·p) = 0`.
The definition is meant only for `p > 0`, `c ≥ 0`; every statement carries those hypotheses. -/
noncomputable def piPC (p c : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then 0
  else if c = 0 then 1 - Real.exp (-p * ((⌊1 + x / p⌋ : ℤ) : ℝ))
  else 1 - Real.exp (-p * ((⌊1 + Real.log (1 + c * x) / (c * p)⌋ : ℤ) : ℝ))

end BalkemaDeHaan.DiscreteDomain
