import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_BestReplyEdge
import Definitions.Def_YoungConventions_AdaptivePlay_IsStrictNash

namespace YoungConventions.AdaptivePlay

/-- **Directed path of length `n` in the best-reply graph from `s` to a strict Nash equilibrium**
(Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84, §4, p. 64, PDF p. 9, in the
definition of `L(s)`: "a shortest directed path in the best reply graph from `s` to a strict Nash
equilibrium").

`IsPathToStrictNash u s n` holds iff there are vertices `s = f₀, f₁, …, fₙ` with an edge
`fⱼ → fⱼ₊₁` of the best-reply graph for every `j < n`, and `fₙ` a strict pure Nash equilibrium.

**Formalization Note.** The path is a function `f : Fin (n + 1) → ∏ Sᵢ`; its length is the number
`n` of edges. Vertices may repeat (a walk); this does not change the shortest length. -/
def IsPathToStrictNash {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) (n : ℕ) : Prop :=
  ∃ f : Fin (n + 1) → ∀ i, S i,
    f 0 = s ∧ IsStrictNash u (f (Fin.last n)) ∧
      ∀ j : Fin n, BestReplyEdge u (f j.castSucc) (f j.succ)

end YoungConventions.AdaptivePlay
