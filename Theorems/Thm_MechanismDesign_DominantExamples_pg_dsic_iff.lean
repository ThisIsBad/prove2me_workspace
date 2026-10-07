import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_PublicGood

namespace MechanismDesign.DominantExamples

/-- Proposition 4.5, p.86. A direct public good mechanism is dominant strategy
incentive-compatible if and only if for every agent `i` and every `θ_{-i} ∈ Θ_{-i}`
(represented by `θ ∈ Θ`, whose `i`-th coordinate is overwritten) there are a real number
`θ̂_i` (possibly outside `[θ̲, θ̄]`) and two payments `τ_i, τ̂_i ∈ ℝ` such that for all
`θ_i ∈ [θ̲, θ̄]`:
`θ_i < θ̂_i ⇒ q(θ_i, θ_{-i}) = 0 and t_i(θ_i, θ_{-i}) = τ_i`;
`θ_i > θ̂_i ⇒ q(θ_i, θ_{-i}) = 1 and t_i(θ_i, θ_{-i}) = τ̂_i`;
`θ_i = θ̂_i ⇒ (q = 0 and t_i = τ_i) or (q = 1 and t_i = τ̂_i)`;
and `τ̂_i − τ_i = θ̂_i`. -/
theorem pg_dsic_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : PublicGoodSetting}
    (M : PublicGoodMechanism E ι) :
    M.IsDSIC ↔ ∀ i, ∀ θ ∈ E.typeSpace ι, ∃ θhat τ τhat : ℝ,
      (∀ x ∈ Set.Icc E.lo E.hi, x < θhat →
        M.q (Function.update θ i x) = 0 ∧ M.t i (Function.update θ i x) = τ) ∧
      (∀ x ∈ Set.Icc E.lo E.hi, θhat < x →
        M.q (Function.update θ i x) = 1 ∧ M.t i (Function.update θ i x) = τhat) ∧
      (∀ x ∈ Set.Icc E.lo E.hi, x = θhat →
        (M.q (Function.update θ i x) = 0 ∧ M.t i (Function.update θ i x) = τ) ∨
        (M.q (Function.update θ i x) = 1 ∧ M.t i (Function.update θ i x) = τhat)) ∧
      τhat - τ = θhat := by sorry

end MechanismDesign.DominantExamples

