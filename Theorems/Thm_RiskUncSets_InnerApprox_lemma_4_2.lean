import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
noncomputable section

namespace RiskUncSets.InnerApprox

/-- Lemma 4.2, (13): `‖a − â‖_{q̃,𝒜} = (1/|λ|) ‖a − â‖_{q,𝒜}` for `q̃ = λq + (1−λ)e_N`,
`q ∈ Δ̂ᴺ_sym`, `λ ≠ 0`. -/
theorem lemma_4_2 {N n : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    (hq : q ∈ symRestrictedSimplex N) (a : Fin N → Fin n → ℝ)
    (lam : ℝ) (hlam : lam ≠ 0) :
    ∀ w : Fin n → ℝ, normQ (mix q lam) a w = (1 / |lam|) * normQ q a w := by sorry

end RiskUncSets.InnerApprox

