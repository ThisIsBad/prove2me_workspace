import Mathlib

namespace NonmonotoneLS.Shared

/-- The parameters of the Nonmonotone Line Search Algorithm (NLSA) of Zhang and Hager
(SIAM J. Optim. 14 (2004), p. 1044, "Initialization"):
`0 ≤ η_min ≤ η_max ≤ 1`, `0 < δ < σ < 1 < ρ` and `μ > 0`. -/
structure Params where
  /-- lower bound `η_min` for the averaging weights `η_k` -/
  ηmin : ℝ
  /-- upper bound `η_max` for the averaging weights `η_k` -/
  ηmax : ℝ
  /-- sufficient-decrease constant `δ` in (1.4) -/
  δ : ℝ
  /-- curvature constant `σ` in (1.5) -/
  σ : ℝ
  /-- expansion factor `ρ > 1` of the Armijo rule -/
  ρ : ℝ
  /-- upper bound `μ` on the Armijo step -/
  μ : ℝ
  ηmin_nonneg : 0 ≤ ηmin
  ηmin_le_ηmax : ηmin ≤ ηmax
  ηmax_le_one : ηmax ≤ 1
  δ_pos : 0 < δ
  δ_lt_σ : δ < σ
  σ_lt_one : σ < 1
  one_lt_ρ : 1 < ρ
  μ_pos : 0 < μ

end NonmonotoneLS.Shared
