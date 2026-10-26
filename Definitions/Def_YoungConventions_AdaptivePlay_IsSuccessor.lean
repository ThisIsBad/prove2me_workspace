import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History

namespace YoungConventions.AdaptivePlay

/-- **Successor of a state** (Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84,
§3, p. 61, PDF p. 6, displayed definition "Successor"): "A *successor* of a state `h ∈ H` is any
state `h′ ∈ H` obtained by deleting the left-most element of `h` and adjoining a new right-most
element."

`IsSuccessor h h'` holds iff `h′ₜ = hₜ₊₁` for every position `t` with `t + 1 < m`; the right-most
entry `h′_{m−1}` (the new play) is arbitrary.

**Formalization Note.** Position `0` is the oldest play (see `History`). -/
def IsSuccessor {ι : Type*} {S : ι → Type*} {m : ℕ} (h h' : History S m) : Prop :=
  ∀ t : Fin m, ∀ ht : t.val + 1 < m, h' t = h ⟨t.val + 1, ht⟩

end YoungConventions.AdaptivePlay
