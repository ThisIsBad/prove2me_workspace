import Mathlib

namespace YoungConventions.AdaptivePlay

/-- **Best reply to `s₋ᵢ`** (Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84,
§4, p. 64, PDF p. 9, in the definition of the best-reply graph: "`s′ᵢ` is a best reply to `s₋ᵢ`").

The strategy `x ∈ Sᵢ` is a best reply of player `i` to the strategies `s₋ᵢ` of the other players
if no strategy `y ∈ Sᵢ` gives `i` a strictly higher payoff against `s₋ᵢ`:
`uᵢ(y, s₋ᵢ) ≤ uᵢ(x, s₋ᵢ)` for all `y`.

**Formalization Note.** The players are a type `ι`, the strategies a family `S : ι → Type*`, and the
payoffs `u : ι → (∀ i, S i) → ℝ` (`u i s` is `uᵢ(s)`, p. 61). The profile `(y, s₋ᵢ)` is
`Function.update s i y`; the `i`-th coordinate of `s` itself is ignored. Best replies are pure
strategies and need not be unique. -/
def IsBestReply {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) (i : ι) (s : ∀ i, S i) (x : S i) : Prop :=
  ∀ y : S i, u i (Function.update s i y) ≤ u i (Function.update s i x)

end YoungConventions.AdaptivePlay
