import Mathlib

namespace LiuVanRyzin

/-- The fill rate as a function of the cutoff `v` under the power utility `u(x) = x ^ γ`
(§3.1, constraint of Eq. (5), from Eq. (2)): `q(v) = ((v - p₁) / (v - p₂)) ^ γ`, meaningful for
`v ≥ p₁ > p₂`. -/
noncomputable def fillRate (p₁ p₂ γ v : ℝ) : ℝ :=
  ((v - p₁) / (v - p₂)) ^ γ

/-- The stocking quantity `C` that induces cutoff `v`, solved from the constraint of Eq. (5)
(§3.1, p. 1122; `C⁰` of Proposition 3): `C(v) = (N / Ū) (Ū - v + (v - p₂) q(v))`. -/
noncomputable def capacity (N Ubar p₁ p₂ γ v : ℝ) : ℝ :=
  (N / Ubar) * (Ubar - v + (v - p₂) * fillRate p₁ p₂ γ v)

/-- The segmented-market profit `Π(v)` of Eq. (6), §3.1, p. 1122:
`Π(v) = (N / Ū) ((p₁ - α)(Ū - v) + (p₂ - α)(v - p₂) ((v - p₁)/(v - p₂)) ^ γ)`. -/
noncomputable def segProfit (N Ubar p₁ p₂ α γ v : ℝ) : ℝ :=
  (N / Ubar) * ((p₁ - α) * (Ubar - v) + (p₂ - α) * (v - p₂) * fillRate p₁ p₂ γ v)

/-- The profit of serving the entire market at the low price only, `Π^NS = (p₂ - α) N F̄(p₂)`
(§2.2, p. 1121), with the uniform law on `[0, Ū]` of §3: `F̄(p₂) = (Ū - p₂) / Ū`. -/
noncomputable def lowPriceProfit (N Ubar p₂ α : ℝ) : ℝ :=
  (p₂ - α) * (N / Ubar) * (Ubar - p₂)

/-- The left-hand side of the first-order condition, Eq. (7), §3.1, p. 1122:
`((v - p₁)/(v - p₂)) ^ γ (1 + γ (p₁ - p₂)/(v - p₁)) - (p₁ - α)/(p₂ - α)`. -/
noncomputable def focLHS (p₁ p₂ α γ v : ℝ) : ℝ :=
  fillRate p₁ p₂ γ v * (1 + γ * (p₁ - p₂) / (v - p₁)) - (p₁ - α) / (p₂ - α)

/-- The critical valuation bound `U_c` of Eq. (8), §3.1, p. 1122, as a function of the root
`v⁰` of Eq. (7):
`U_c = ((p₂ + γ(p₁ - α)) v⁰ - p₂ (p₁ + γ(p₂ - α))) / (v⁰ - p₁ + γ(p₁ - p₂))`. -/
noncomputable def criticalU (p₁ p₂ α γ v₀ : ℝ) : ℝ :=
  ((p₂ + γ * (p₁ - α)) * v₀ - p₂ * (p₁ + γ * (p₂ - α))) / (v₀ - p₁ + γ * (p₁ - p₂))

end LiuVanRyzin
