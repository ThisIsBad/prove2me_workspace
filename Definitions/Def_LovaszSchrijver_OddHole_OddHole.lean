import Mathlib

namespace LovaszSchrijver.OddHole

/-- `C` induces a chordless odd cycle in `G` (an odd hole, p. 175): for some odd `m ≥ 3`
there is a bijection `f : Fin m ≃ C` under which two vertices of `C` are adjacent in `G`
exactly when their indices are consecutive modulo `m`. Triangles (`m = 3`) are included. -/
def IsOddHole {V : Type} (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ ∃ f : Fin m ≃ C, ∀ s t : Fin m,
    G.Adj (f s).1 (f t).1 ↔ (t.val = (s.val + 1) % m ∨ s.val = (t.val + 1) % m)

end LovaszSchrijver.OddHole
