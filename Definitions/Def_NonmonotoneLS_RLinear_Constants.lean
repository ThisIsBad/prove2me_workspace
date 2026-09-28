import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params

namespace NonmonotoneLS.RLinear

/-- The constant `β` of Eq. (2.9) (p. 1047):
`β = min{δμc₁/ρ, 2δ(1-δ)c₁²/(Lρc₂²), δ(1-σ)c₁²/(Lc₂²)}`. -/
noncomputable def beta (p : Shared.Params) (c₁ c₂ L : ℝ) : ℝ :=
  min (min (p.δ * p.μ * c₁ / p.ρ) (2 * p.δ * (1 - p.δ) * c₁ ^ 2 / (L * p.ρ * c₂ ^ 2)))
    (p.δ * (1 - p.σ) * c₁ ^ 2 / (L * c₂ ^ 2))

/-- The constant `b = 1 + μc₂L` of Eq. (3.7) (p. 1050). -/
def bConst (p : Shared.Params) (c₂ L : ℝ) : ℝ :=
  1 + p.μ * c₂ * L

/-- The constant `b₂ = 1/(β + γb²)` of (3.8) (p. 1050). -/
noncomputable def b2Const (p : Shared.Params) (c₁ c₂ L γ : ℝ) : ℝ :=
  1 / (beta p c₁ c₂ L + γ * bConst p c₂ L ^ 2)

/-- The contraction factor `θ = 1 - βb₂(1 - η_max)` of (3.8) (p. 1050). -/
noncomputable def theta (p : Shared.Params) (c₁ c₂ L γ : ℝ) : ℝ :=
  1 - beta p c₁ c₂ L * b2Const p c₁ c₂ L γ * (1 - p.ηmax)

end NonmonotoneLS.RLinear
