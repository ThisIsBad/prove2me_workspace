import Mathlib

namespace CachonCoord.InternalMarket

/-- Total retailer revenue `π(γ, α, Q)` (Cachon 2003, 3rd draft, §6.9.1, p. 92) when retailer one
receives `γQ` units and retailer two `(1 − γ)Q` units of the output `Q`:
`π(γ, α, Q) = (α₁ γ^{(η−1)/η} + α₂ (1 − γ)^{(η−1)/η}) Q^{(η−1)/η}`.
Here `η > 1` is the constant demand elasticity and `α₁, α₂ > 0` the demand realizations;
all powers are real powers (`Real.rpow`), meant for `γ ∈ [0, 1]` and `Q ≥ 0`. -/
noncomputable def revenue (η α₁ α₂ γ Q : ℝ) : ℝ :=
  (α₁ * γ ^ ((η - 1) / η) + α₂ * (1 - γ) ^ ((η - 1) / η)) * Q ^ ((η - 1) / η)

/-- The share `γ°(α) = α₁^η / (α₁^η + α₂^η)` of output allocated to retailer one, Eq. (44)
(§6.9.1, p. 93). Defined by the printed formula; that it is the optimal share is a theorem. -/
noncomputable def optShare (η α₁ α₂ : ℝ) : ℝ :=
  α₁ ^ η / (α₁ ^ η + α₂ ^ η)

/-- Total retailer revenue conditional on the allocation `γ°(α)`:
`π(α, Q) = π(γ°(α), α, Q)` (§6.9.1, p. 93). Its closed form is a theorem. -/
noncomputable def optRevenue (η α₁ α₂ Q : ℝ) : ℝ :=
  revenue η α₁ α₂ (optShare η α₁ α₂) Q

/-- Retailer `i`'s profit when he buys `qᵢ` units at the per-unit price `w` and has demand
realization `αᵢ` (§6.9.1, p. 93): `πᵢ(qᵢ, w) = αᵢ qᵢ^{(η−1)/η} − w qᵢ`
(revenue `qᵢ pᵢ(qᵢ)` with `pᵢ(qᵢ) = αᵢ qᵢ^{−1/η}`, p. 92). Meant for `qᵢ ≥ 0`. -/
noncomputable def retailerProfit (η αᵢ w q : ℝ) : ℝ :=
  αᵢ * q ^ ((η - 1) / η) - w * q

/-- The contingent transfer price
`w(α, Q) = ((η − 1)/η) (α₁^η + α₂^η)^{1/η} Q^{−1/η}` (§6.9.1, p. 93), meant for `Q > 0`. -/
noncomputable def price (η α₁ α₂ Q : ℝ) : ℝ :=
  ((η - 1) / η) * (α₁ ^ η + α₂ ^ η) ^ (1 / η) * Q ^ (-1 / η)

end CachonCoord.InternalMarket
