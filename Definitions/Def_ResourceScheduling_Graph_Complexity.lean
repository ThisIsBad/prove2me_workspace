import Mathlib
import Definitions.Def_CookPvsNP_defs

/-!
# NP-hardness and NP-hardness in the strong sense

On top of Cook's P/NP layer (`CookPvsNP`). A language is NP-hard when every NP language over a
finite nonempty alphabet reduces to it in polynomial time (the second conjunct of
`CookPvsNP.NPComplete`). A decision problem, given by a predicate `Yes` on its instances and a
**unary** encoding `enc` over the two-letter alphabet `Letter`, is NP-hard in the strong sense
(Garey & Johnson, *Computers and Intractability*, 1979, §4.2) when the language of codes of its
yes-instances is NP-hard: with every number written in unary, `Max(I) ≤ Length(I)`, so the
restriction to instances whose numbers are polynomially bounded in the instance length is the
whole problem.
-/

namespace ResourceScheduling.Graph

open CookPvsNP

/-- NP-hardness: every language in `NP`, over any finite nonempty alphabet, is polynomial-time
many-one reducible to `L`. -/
def NPHard {S : Type} (L : Lang S) : Prop :=
  ∀ (S' : Type) [Fintype S'] [Nonempty S'] (L' : Lang S'), L' ∈ NP S' → PolyReducible L' L

/-- The two-letter alphabet of the unary encodings: `one` is a unary digit (or a 1-bit),
`sep` closes a number (or is a 0-bit). -/
inductive Letter where
  | one
  | sep
  deriving DecidableEq

instance : Fintype Letter where
  elems := {Letter.one, Letter.sep}
  complete := by intro x; cases x <;> simp

instance : Nonempty Letter := ⟨Letter.one⟩

/-- The unary code of a natural number `k`: `k` copies of `one` followed by `sep`. -/
def unary (k : ℕ) : List Letter :=
  List.replicate k Letter.one ++ [Letter.sep]

/-- The language of codes of the yes-instances of a decision problem. It contains only
well-formed codes. -/
def codeLang {α : Type} (Yes : α → Prop) (enc : α → List Letter) : Lang Letter :=
  { w | ∃ x, Yes x ∧ w = enc x }

/-- NP-hardness in the strong sense of the decision problem `Yes`, encoded by the unary
encoding `enc`: the language of codes of yes-instances is NP-hard. It is Garey–Johnson's strong
NP-hardness only when `enc` writes every number in unary, which is the case for every encoding
this development applies it to. -/
def StronglyNPHard {α : Type} (Yes : α → Prop) (enc : α → List Letter) : Prop :=
  NPHard (codeLang Yes enc)

end ResourceScheduling.Graph
