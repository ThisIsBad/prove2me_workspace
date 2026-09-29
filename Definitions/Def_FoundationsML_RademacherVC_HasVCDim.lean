import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_GrowthFunction

namespace FoundationsML.RademacherVC

/-- `H` has VC-dimension `d` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 3.10, p. 36, PDF p. 53):
`VCdim(H) = max{m : Π_H(m) = 2^m}`, the size of the largest set of points `H` shatters.

**Formalization Note.** `HasVCDim H d` states `d` is such a maximum directly: `Π_H(d) = 2^d`
(a set of size `d` is shattered) and every `m` with `Π_H(m) = 2^m` satisfies `m ≤ d` (`d` is
the largest such size). This is a Prop parametrized by the candidate dimension `d : ℕ` rather
than a total `ℕ`-valued (or `ℕ∞`-valued) function, so it does not assign a value to the book's
`VCdim(H) = +∞` case (Examples 3.15–3.16); every theorem in this chunk that uses `HasVCDim`
takes it as a hypothesis, matching the book's own "let `H` be a hypothesis set with
`VCdim(H) = d`" (implicitly a finite `d`). -/
def HasVCDim {X : Type*} (H : Set (X → Bool)) (d : ℕ) : Prop :=
  GrowthFunction H d = 2 ^ d ∧ ∀ m : ℕ, GrowthFunction H m = 2 ^ m → m ≤ d

end FoundationsML.RademacherVC
