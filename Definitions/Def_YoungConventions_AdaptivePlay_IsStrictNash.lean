import Mathlib

namespace YoungConventions.AdaptivePlay

/-- **Strict pure strategy Nash equilibrium** (Young 1993, *The Evolution of Conventions*,
Econometrica 61:57–84, §4, p. 62, PDF p. 7: "a strict pure strategy Nash equilibrium").

The pure strategy tuple `s ∈ ∏ Sᵢ` is a strict Nash equilibrium if every unilateral deviation
strictly lowers the deviator's payoff: for every player `i` and every `y ∈ Sᵢ` with `y ≠ sᵢ`,
`uᵢ(y, s₋ᵢ) < uᵢ(s)`. Equivalently, each `sᵢ` is the *unique* best reply to `s₋ᵢ`, which is how the
paper's argument on p. 62 uses the term.

**Formalization Note.** The paper uses the standard notion without a display. The profile
`(y, s₋ᵢ)` is `Function.update s i y`. -/
def IsStrictNash {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ i : ι, ∀ y : S i, y ≠ s i → u i (Function.update s i y) < u i s

end YoungConventions.AdaptivePlay
