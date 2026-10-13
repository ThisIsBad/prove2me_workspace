import Mathlib

namespace UnrelatedSched.TwoTimes

/-- A matching of an instance of q-dimensional matching (Lenstra, Shmoys, Tardos, CWI Report
OS-R8714 (1987), §5, proof of Theorem 7, p. 8: "a matching instance with m q-tuples over a ground
set of qn elements").

The ground set is `Fin (q * n)` and the family is `S : Fin m → Finset (Fin (q * n))`, indexed by
`i : Fin m` (repeated sets allowed); the theorems that use it assume `(S i).card = q`. A matching is
a subfamily, given by its index set `F' : Finset (Fin m)`, with `|F'| = n` whose union is the whole
ground set. The q-partite structure of q-dimensional matching is not imposed: families of q-sets
include the q-partite families. -/
def IsQMatching {q n m : ℕ} (S : Fin m → Finset (Fin (q * n))) (F' : Finset (Fin m)) : Prop :=
  F'.card = n ∧ F'.biUnion S = Finset.univ

/-- The element job of the scheduling instance of Theorem 7 corresponding to the element
`u` of the ground set. The `qn + p(m - n)` jobs are enumerated as `Fin (q * n + p * (m - n))`,
the `qn` element jobs first, then the `p(m - n)` dummy jobs. -/
def elemJob (p q n m : ℕ) (u : Fin (q * n)) : Fin (q * n + p * (m - n)) :=
  finSumFinEquiv (Sum.inl u)

/-- The `k`-th dummy job of the scheduling instance of Theorem 7, `k : Fin (p * (m - n))`. -/
def dummyJob (p q n m : ℕ) (k : Fin (p * (m - n))) : Fin (q * n + p * (m - n)) :=
  finSumFinEquiv (Sum.inr k)

/-- The processing times of the scheduling instance built in the proof of Theorem 7 (pp. 8–9)
from a q-dimensional matching instance `S` with `m` tuples over a ground set of `qn` elements:
`m` machines (machine `i` corresponds to the tuple `S i`), `qn` element jobs and `p(m - n)` dummy
jobs. An element job takes `p` time units on each machine whose tuple contains the corresponding
element; all other processing times are `q` time units. -/
def twoTimes (p q n : ℕ) {m : ℕ} (S : Fin m → Finset (Fin (q * n))) :
    Matrix (Fin m) (Fin (q * n + p * (m - n))) ℕ :=
  fun i j => Sum.elim (fun u => if u ∈ S i then p else q) (fun _ => q) (finSumFinEquiv.symm j)

@[simp] theorem twoTimes_elem (p q n : ℕ) {m : ℕ} (S : Fin m → Finset (Fin (q * n))) (i : Fin m)
    (u : Fin (q * n)) : twoTimes p q n S i (elemJob p q n m u) = if u ∈ S i then p else q := by
  simp [twoTimes, elemJob]

@[simp] theorem twoTimes_dummy (p q n : ℕ) {m : ℕ} (S : Fin m → Finset (Fin (q * n))) (i : Fin m)
    (k : Fin (p * (m - n))) : twoTimes p q n S i (dummyJob p q n m k) = q := by
  simp [twoTimes, dummyJob]

end UnrelatedSched.TwoTimes
