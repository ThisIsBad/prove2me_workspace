import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.5 (p.135): if `q` is weakly monotone in every `θᵢ` (for every agent
`i` and every `θ₋ᵢ`, the rule `θᵢ ↦ q(θᵢ, θ₋ᵢ)` is weakly monotone in the sense of
Definition 5.4 for agent `i`'s utility), then `q` satisfies positive association of differences. -/
theorem weakly_monotone_pad {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) (hq : WeaklyMonotoneInEvery u q) :
    PAD u q := by sorry

end MechanismDesign.VCG

