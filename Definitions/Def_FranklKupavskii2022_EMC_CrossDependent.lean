import Mathlib

namespace FranklKupavskii2022.EMC

/-- Cross-dependent families (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 4, p. 9): "families
F_1, …, F_{s+1} are cross-dependent, if there are no F_1 ∈ F_1, …, F_{s+1} ∈ F_{s+1} such that
F_1, …, F_{s+1} are pairwise disjoint."

**Formalization Note.** The `s + 1` families are `Fam 1, …, Fam (s + 1)` for
`Fam : ℕ → Finset (Finset ℕ)` (values outside `1..s+1` are ignored). Pairwise disjointness is
indexed by position: a choice `f i ∈ Fam i` with `f i` and `f j` disjoint for all `i ≠ j` in
`1..s+1` (so two chosen sets can only coincide if both are empty). -/
def CrossDependent (s : ℕ) (Fam : ℕ → Finset (Finset ℕ)) : Prop :=
  ¬ ∃ f : ℕ → Finset ℕ, (∀ i ∈ Finset.Icc 1 (s + 1), f i ∈ Fam i) ∧
    ∀ i ∈ Finset.Icc 1 (s + 1), ∀ j ∈ Finset.Icc 1 (s + 1), i ≠ j → Disjoint (f i) (f j)

end FranklKupavskii2022.EMC
