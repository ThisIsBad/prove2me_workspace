import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace SetCoverThreshold.SetCover

/-- Gap (promise) NP-hardness, Karp style: every NP language over every finite nonempty alphabet
maps in polynomial time to instances satisfying `Yes` (members) and `No` (non-members).
"It is NP-hard to distinguish between `Yes` and `No`" (Feige 1998, Theorem 2.1.1, Prop. 2.1.2). -/
def GapNPHard {α Sym : Type} (enc : α → List Sym) (Yes No : α → Prop) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
    L' ∈ CookPvsNP.NP Sym' →
      ∃ f : List Sym' → α, CookPvsNP.PolyTimeComputable (fun x => enc (f x)) ∧
        ∀ x, (x ∈ L' → Yes (f x)) ∧ (x ∉ L' → No (f x))

/-- The class `TIME(n^{O(log log n)})` (Feige 1998, p. 636): languages decided by a deterministic
one-tape Turing machine (in the sense of `CookPvsNP`) that halts on every input `w` within
`|w|^(c * (⌊log₂ ⌊log₂ |w|⌋⌋ + 1)) + c` steps, for some constant `c`. -/
def LogLogTime (Sym : Type) [Fintype Sym] : Set (CookPvsNP.Lang Sym) :=
  { L | ∃ (Γ : Type) (_ : Fintype Γ) (ι : Sym ↪ Γ) (M : CookPvsNP.TM Γ) (c : ℕ),
      (∀ w : List Sym,
        M.HaltsWithin (w.length ^ (c * (Nat.log 2 (Nat.log 2 w.length) + 1)) + c) (w.map ι)) ∧
      ∀ w : List Sym, w ∈ L ↔ M.Accepts (w.map ι) }

end SetCoverThreshold.SetCover
