import Mathlib

namespace FranklKupavskii2022.EMC

/-- The matching number `ν(F)` of a family of finite sets (Frankl–Kupavskii, *The Erdős Matching
Conjecture and concentration inequalities*, arXiv:1806.08855v3, Sect. 1, p. 1): "A matching in F
is a collection of pairwise disjoint sets in F. We denote by ν(F) the matching number of F, that
is, the maximum size of a matching in F."

**Formalization Note.** A matching is a *subfamily* `M ⊆ F` whose distinct members are pairwise
disjoint, so its members are distinct sets; `ν(F)` is the largest cardinality of such a
subfamily (a finite maximum; `ν(∅) = 0`). A family containing `∅` has `ν ≥ 1`, since `{∅}` is
a matching of size one. -/
def matchingNumber (F : Finset (Finset ℕ)) : ℕ :=
  (F.powerset.filter (fun M => ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B)).sup Finset.card

end FranklKupavskii2022.EMC
