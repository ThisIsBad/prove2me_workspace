import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.2 (p.132): suppose `A` is finite, for every agent `i` let `Rᵢ` be an
order (complete and transitive) of `A`, and suppose every type set `Θᵢ` is bounded and
one-dimensional with respect to `Rᵢ`. Then there are transfer rules making `(q, t₁, …, t_N)`
dominant strategy incentive-compatible if and only if, for every `i` and every `θ₋ᵢ`, the rule
`θᵢ ↦ q(θᵢ, θ₋ᵢ)` is monotone with respect to `Rᵢ`. -/
theorem dsic_iff_monotone_one_dimensional {ι A : Type*} {Θ : ι → Type*} [Fintype ι]
    [DecidableEq ι] [Finite A] (u : ∀ i, A → Θ i → ℝ) (R : ι → A → A → Prop)
    (hR : ∀ i, IsCompleteOrder (R i)) (hbdd : ∀ i, BoundedTypes (u i))
    (h1d : ∀ i, OneDimensional (R i) (u i)) (q : (∀ i, Θ i) → A) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩) ↔
      ∀ (i : ι) (θ : ∀ j, Θ j),
        MonotoneWRT (R i) (u i) (fun x : Θ i => q (Function.update θ i x)) := by sorry

end MechanismDesign.VCG

