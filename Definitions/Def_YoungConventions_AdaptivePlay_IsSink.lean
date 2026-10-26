import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_BestReplyEdge

namespace YoungConventions.AdaptivePlay

/-- **Sink of the best-reply graph** (Young 1993, *The Evolution of Conventions*, Econometrica
61:57–84, §4, p. 64, PDF p. 9: "some vertex `s*` from which there is no exiting edge (a *sink*)").

The vertex `s` is a sink if there is no edge `s → s′` of the best-reply graph. -/
def IsSink {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ s' : ∀ i, S i, ¬ BestReplyEdge u s s'

end YoungConventions.AdaptivePlay
