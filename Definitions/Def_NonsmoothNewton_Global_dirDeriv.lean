import Mathlib

namespace NonsmoothNewton.Global

open Filter Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- `HasDirDerivAt F x h d`: the classical one-sided directional derivative of `F` at `x` in
direction `h` exists and equals `d`, i.e. `(F (x + t h) - F x) / t → d` as `t ↓ 0`
(Qi–Sun 1993, p. 355, Eq. (2.4)). -/
def HasDirDerivAt (F : E → G) (x h : E) (d : G) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (F (x + t • h) - F x)) (𝓝[>] 0) (𝓝 d)

/-- `dirDeriv F x h` is the paper's `F'(x; h) = lim_{t ↓ 0} (F (x + t h) - F x) / t`
(Eq. (2.4)), taken as `limUnder` along `t ↓ 0`. It is the true one-sided directional derivative
only when that limit exists; this file uses it only where semismoothness guarantees existence
(Eq. (2.7), p. 355). -/
noncomputable def dirDeriv (F : E → G) (x h : E) : G :=
  limUnder (𝓝[>] (0 : ℝ)) (fun t : ℝ => t⁻¹ • (F (x + t • h) - F x))

end NonsmoothNewton.Global
