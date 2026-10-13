import Mathlib

namespace UnrelatedSched.ThreeHalves

/-- A matching of an instance of 3-DIMENSIONAL MATCHING (Lenstra, Shmoys, Tardos, CWI Report
OS-R8714 (1987), §4, p. 7, proof of Theorem 4).

The instance consists of disjoint sets `A = {a_1, …, a_n}`, `B = {b_1, …, b_n}`,
`C = {c_1, …, c_n}` and a family `F = {T_1, …, T_m}` of triples with one element in each of
`A`, `B`, `C`. Here the elements `a_j`, `b_k`, `c_l` are indexed by `j, k, l : Fin n`, and the
triple `T_i` is `T i = (j, k, l)`, standing for `(a_j, b_k, c_l)`; the triples are indexed by
`i : Fin m`, so the same triple may occur several times in the family.

A matching is a subfamily `F' ⊆ F`, given by its index set `F' : Finset (Fin m)`, with `|F'| = n`
whose union is `A ∪ B ∪ C`: every `a_j`, every `b_k` and every `c_l` lies in some triple of `F'`.
(With `|F'| = n` this covering condition forces the triples of `F'` to be pairwise disjoint.) -/
def IsMatching {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (F' : Finset (Fin m)) : Prop :=
  F'.card = n ∧
    (∀ j : Fin n, ∃ i ∈ F', (T i).1 = j) ∧
    (∀ k : Fin n, ∃ i ∈ F', (T i).2.1 = k) ∧
    (∀ l : Fin n, ∃ i ∈ F', (T i).2.2 = l)

/-- The instance `T` of 3-DIMENSIONAL MATCHING has a matching (the question of the problem). -/
def HasMatching {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) : Prop :=
  ∃ F' : Finset (Fin m), IsMatching T F'

end UnrelatedSched.ThreeHalves
