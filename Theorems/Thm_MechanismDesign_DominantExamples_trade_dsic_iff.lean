import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_BilateralTrade

namespace MechanismDesign.DominantExamples

/-- Proposition 4.9, p.91. A direct bilateral trade mechanism is dominant strategy
incentive-compatible if and only if
for every `θ_B ∈ [θ̲_B, θ̄_B]` there are a real number `θ̂_S` and payments `τ_S, τ̂_S ∈ ℝ`
such that for all `θ_S ∈ [θ̲_S, θ̄_S]`:
`θ_S < θ̂_S ⇒ q(θ) = 1 and t_S(θ) = τ̂_S`; `θ_S > θ̂_S ⇒ q(θ) = 0 and t_S(θ) = τ_S`;
`θ_S = θ̂_S ⇒ (q(θ) = 0 and t_S(θ) = τ_S) or (q(θ) = 1 and t_S(θ) = τ̂_S)`;
and `τ̂_S − τ_S = θ̂_S`;
and for every `θ_S ∈ [θ̲_S, θ̄_S]` there are a real number `θ̂_B` and payments
`τ_B, τ̂_B ∈ ℝ` such that for all `θ_B ∈ [θ̲_B, θ̄_B]`:
`θ_B < θ̂_B ⇒ q(θ) = 0 and t_B(θ) = τ_B`; `θ_B > θ̂_B ⇒ q(θ) = 1 and t_B(θ) = τ̂_B`;
`θ_B = θ̂_B ⇒ (q(θ) = 0 and t_B(θ) = τ_B) or (q(θ) = 1 and t_B(θ) = τ̂_B)`;
and `τ̂_B − τ_B = θ̂_B`. Here `θ = (θ_S, θ_B)`. -/
theorem trade_dsic_iff {E : TradeSetting} (M : TradeMechanism E) :
    M.IsDSIC ↔
      (∀ θB ∈ Set.Icc E.loB E.hiB, ∃ θhatS τS τhatS : ℝ,
        (∀ θS ∈ Set.Icc E.loS E.hiS, θS < θhatS →
          M.q (θS, θB) = 1 ∧ M.tS (θS, θB) = τhatS) ∧
        (∀ θS ∈ Set.Icc E.loS E.hiS, θhatS < θS →
          M.q (θS, θB) = 0 ∧ M.tS (θS, θB) = τS) ∧
        (∀ θS ∈ Set.Icc E.loS E.hiS, θS = θhatS →
          (M.q (θS, θB) = 0 ∧ M.tS (θS, θB) = τS) ∨
          (M.q (θS, θB) = 1 ∧ M.tS (θS, θB) = τhatS)) ∧
        τhatS - τS = θhatS) ∧
      (∀ θS ∈ Set.Icc E.loS E.hiS, ∃ θhatB τB τhatB : ℝ,
        (∀ θB ∈ Set.Icc E.loB E.hiB, θB < θhatB →
          M.q (θS, θB) = 0 ∧ M.tB (θS, θB) = τB) ∧
        (∀ θB ∈ Set.Icc E.loB E.hiB, θhatB < θB →
          M.q (θS, θB) = 1 ∧ M.tB (θS, θB) = τhatB) ∧
        (∀ θB ∈ Set.Icc E.loB E.hiB, θB = θhatB →
          (M.q (θS, θB) = 0 ∧ M.tB (θS, θB) = τB) ∨
          (M.q (θS, θB) = 1 ∧ M.tB (θS, θB) = τhatB)) ∧
        τhatB - τB = θhatB) := by sorry

end MechanismDesign.DominantExamples

