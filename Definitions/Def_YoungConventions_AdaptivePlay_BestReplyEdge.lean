import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReply

namespace YoungConventions.AdaptivePlay

/-- **Edge of the best-reply graph** (Young 1993, *The Evolution of Conventions*, Econometrica
61:57–84, §4, p. 64, PDF p. 9): "each vertex is an `n`-tuple of strategies `s ∈ ∏Sᵢ`, and for
every two vertices `s` and `s′` there is a directed edge `s → s′` if and only if `s ≠ s′` and there
exists exactly one agent `i` such that `s′ᵢ` is a best reply to `s₋ᵢ` and `s′₋ᵢ = s₋ᵢ`."

`BestReplyEdge u s s'` holds iff some player `i` and some strategy `x ≠ sᵢ` that is a best reply of
`i` to `s₋ᵢ` give `s′ = (x, s₋ᵢ)`.

**Formalization Note.** Equivalence with the page: if `s ≠ s′` and `s′₋ᵢ = s₋ᵢ`, then `s` and `s′`
differ exactly in coordinate `i`, so the agent `i` is automatically unique and "exactly one" adds
nothing; and `s ≠ s′` with `s′ = (x, s₋ᵢ)` is `x ≠ sᵢ`. Best replies are pure best replies
(`IsBestReply`), not best replies to a sample. -/
def BestReplyEdge {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) (s s' : ∀ i, S i) : Prop :=
  ∃ (i : ι) (x : S i), x ≠ s i ∧ IsBestReply u i s x ∧ s' = Function.update s i x

end YoungConventions.AdaptivePlay
