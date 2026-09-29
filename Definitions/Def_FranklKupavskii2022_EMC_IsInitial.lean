import Mathlib

namespace FranklKupavskii2022.EMC

/-- The shifting partial order `A ≺ B` on sets of equal size (Frankl–Kupavskii,
arXiv:1806.08855v3, Sect. 2, p. 3): "(a_1, …, a_k) precedes (b_1, …, b_k) if a_i ≤ b_i for all
i ∈ [k] and the two k-sets are distinct. One can define this for unordered sets A, B by simply
comparing their elements after ordering them increasingly."

**Formalization Note.** Both sets are listed increasingly (`Finset.sort`) and compared entrywise
with `List.Forall₂ (· ≤ ·)`; `Forall₂` forces the two lists to have equal length, so `A ≺ B`
implies `|A| = |B|`. -/
def Precedes (A B : Finset ℕ) : Prop :=
  List.Forall₂ (· ≤ ·) A.sort B.sort ∧ A ≠ B

/-- Initial (shifted) families (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 2, p. 3): "A family
F ⊂ \binom{[m]}{k} is called initial (shifted) if G ≺ F ∈ F implies G ∈ F."

**Formalization Note.** The downward closure ranges over `k`-subsets `G` of `[m] = Finset.Icc 1 m`
only, as in the paper, where every set is a subset of `[m]`. (A `k`-set of naturals containing
`0` precedes members of `F` but is not a subset of `[m]`.) The requirement `F ⊆ \binom{[m]}{k}`
is not part of this predicate; the theorems state it separately. -/
def IsInitial (m k : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  ∀ G ∈ (Finset.Icc 1 m).powersetCard k, ∀ F' ∈ F, Precedes G F' → G ∈ F

end FranklKupavskii2022.EMC
