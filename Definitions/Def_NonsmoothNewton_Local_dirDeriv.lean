import Mathlib
open Filter Topology

namespace NonsmoothNewton.Local

/-- The one-sided (classic) directional derivative of Qi–Sun (1993), Eq. (2.4), p. 355:
`HasDirDerivAt F x h d` means `d = F'(x; h) = lim_{t ↓ 0} (F (x + t h) - F x) / t`.
The limit is taken over `t > 0` only (it is *not* Mathlib's two-sided `lineDeriv`). -/
def HasDirDerivAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x h : E) (d : G) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (F (x + t • h) - F x)) (𝓝[>] 0) (𝓝 d)

/-- The value `F'(x; h)` of the one-sided directional derivative (2.4), as a `limUnder`.
It is meaningful only when the limit exists (`∃ d, HasDirDerivAt F x h d`); every statement
using it carries a hypothesis guaranteeing that. -/
noncomputable def dirDeriv {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x h : E) : G :=
  limUnder (𝓝[>] (0 : ℝ)) (fun t : ℝ => t⁻¹ • (F (x + t • h) - F x))

end NonsmoothNewton.Local
