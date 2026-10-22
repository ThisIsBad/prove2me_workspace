import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
noncomputable section

namespace RiskUncSets.InnerApprox

/-- Proposition 4.2: for `q ∈ Δ̂ᴺ_sym` the gauge (12) of `π̃_q(𝒜)` is a norm, provided
`Π_q(𝒜)` has nonempty interior (added: otherwise (12) is `+∞` off `0`). -/
theorem proposition_4_2 {N n : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    (hq : q ∈ symRestrictedSimplex N) (a : Fin N → Fin n → ℝ)
    (hint : (interior (permutohull q a)).Nonempty) :
    (∀ w : Fin n → ℝ, normQ q a w = 0 ↔ w = 0) ∧
    (∀ (β : ℝ) (w : Fin n → ℝ), normQ q a (β • w) = |β| * normQ q a w) ∧
    ∀ w₁ w₂ : Fin n → ℝ, normQ q a (w₁ + w₂) ≤ normQ q a w₁ + normQ q a w₂ := by sorry

end RiskUncSets.InnerApprox

