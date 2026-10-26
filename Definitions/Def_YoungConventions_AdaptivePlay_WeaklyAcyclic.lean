import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsSink

namespace YoungConventions.AdaptivePlay

/-- **Weakly acyclic game** (Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84,
§4, p. 64, PDF p. 9, displayed definition "Acyclic Game"): "It is *weakly acyclic* if, from any
initial vertex `s`, there exists a directed path to some vertex `s*` from which there is no exiting
edge (a *sink*)."

`WeaklyAcyclic u` holds iff for every strategy tuple `s` there is a sink `s*` of the best-reply
graph reachable from `s` by a directed path (possibly of length zero, when `s` itself is a sink).

**Formalization Note.** Directed paths are the reflexive–transitive closure
`Relation.ReflTransGen` of `BestReplyEdge u`. A path of length zero is allowed: a vertex that is
itself a sink trivially "has a path to a sink". -/
def WeaklyAcyclic {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) : Prop :=
  ∀ s : ∀ i, S i, ∃ s' : ∀ i, S i, Relation.ReflTransGen (BestReplyEdge u) s s' ∧ IsSink u s'

end YoungConventions.AdaptivePlay
