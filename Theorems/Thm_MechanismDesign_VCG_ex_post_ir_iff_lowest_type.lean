import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.9 (pp.137–138): fix an agent `i` and an order (complete, transitive)
`R` of `A` such that `Θᵢ` is one-dimensional with respect to `R`. Suppose `θ̲ᵢ` is the lowest
type (`θᵢ ≻_R θ̲ᵢ` for every `θᵢ ≠ θ̲ᵢ`) and `a̲ᵢ` is the lowest alternative (`b R a̲ᵢ` for every
`b ≠ a̲ᵢ`). Then a dominant strategy incentive-compatible mechanism satisfies agent `i`'s ex post
individual rationality constraint with outside option `a̲ᵢ` if and only if
`uᵢ(q(θ̲ᵢ, θ₋ᵢ), θ̲ᵢ) − tᵢ(θ̲ᵢ, θ₋ᵢ) ≥ uᵢ(a̲ᵢ, θ̲ᵢ)` for every `θ₋ᵢ`. -/
theorem ex_post_ir_iff_lowest_type {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism Θ A) (hM : DSIC u M) (i : ι)
    (R : A → A → Prop) (hR : IsCompleteOrder R) (h1d : OneDimensional R (u i))
    (θlow : Θ i) (hθlow : ∀ x : Θ i, x ≠ θlow → HigherType R (u i) x θlow)
    (alow : A) (halow : ∀ b : A, b ≠ alow → R b alow) :
    ExPostIRAgent u M i alow ↔
      ∀ θ : ∀ j, Θ j, u i (M.q (Function.update θ i θlow)) θlow
        - M.t i (Function.update θ i θlow) ≥ u i alow θlow := by sorry

end MechanismDesign.VCG

