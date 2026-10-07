import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace SchedComplexity.Partition

open ProjSchedTW.Complexity (BSym encNats)

/-- PARTITION (Brucker, Lenstra & Rinnooy Kan 1975, Theorem 2(a), p. 14): the integers
`a_1, …, a_t` (the list `a`, `t = a.length`, indices `j < t`) admit a subset `S` of the
index set `T` with `Σ_{j ∈ S} a_j = Σ_{j ∈ T - S} a_j`. The paper's `S ⊂ T` means "subset";
`S` ranges over all subsets of `T`, including `∅` and `T`. Positivity of the `a_j` is part of
the language `partitionLang`, not of this predicate. -/
def PartitionSolvable (a : List ℕ) : Prop :=
  ∃ S : Finset (Fin a.length), ∑ j ∈ S, a.get j = ∑ j ∈ Sᶜ, a.get j

/-- The PARTITION language (Theorem 2(a), p. 14): the binary codes `encNats [a_1, …, a_t]` of
the lists of **positive** integers that admit a partition. A code of a list with a zero entry is
not in the language. -/
def partitionLang : CookPvsNP.Lang BSym :=
  { c | ∃ a : List ℕ, (∀ x ∈ a, 0 < x) ∧ PartitionSolvable a ∧ c = encNats a }

end SchedComplexity.Partition
