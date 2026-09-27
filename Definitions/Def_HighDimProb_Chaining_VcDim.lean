import Mathlib
import Definitions.Def_HighDimProb_Chaining_Shatters

namespace HighDimProb.Chaining

/-- The **VC dimension** `vc(F)` of a class `F` of Boolean functions on `Ω`: the largest
cardinality of a subset `Λ ⊆ Ω` shattered by `F`. Vershynin, *High-Dimensional Probability*
(2018), Definition 8.3.1, p. 200 (PDF p. 208): "The VC dimension of `F`, denoted `vc(F)`, is the
largest cardinality of a subset `Λ ⊆ Ω` shattered by `F`," with the book's own footnote 1: "If
the largest cardinality does not exist, we set `vc(F) = ∞`." Valued in `ℕ∞ = WithTop ℕ` via
`Set.encard` (which is already `⊤` on an infinite `Λ`) and a supremum over the subtype of
shattered subsets: the supremum of an unbounded or empty family in the complete lattice `ℕ∞`
reproduces the book's footnote exactly (`vc(F) = 0` when only `Λ = ∅`, vacuously shattered by
every `F`, achieves the supremum; `vc(F) = ⊤` when arbitrarily large finite, or some infinite,
`Λ` is shattered), with no case split needed. -/
noncomputable def vcDim {Ω : Type} (F : Set (Ω → Bool)) : ℕ∞ :=
  ⨆ (Λ : {Λ : Set Ω // Shatters F Λ}), Λ.1.encard

end HighDimProb.Chaining
