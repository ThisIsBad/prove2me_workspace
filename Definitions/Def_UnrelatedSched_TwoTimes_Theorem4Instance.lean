import Mathlib

namespace UnrelatedSched.TwoTimes

/-- A matching of an instance of 3-DIMENSIONAL MATCHING (Lenstra, Shmoys, Tardos, CWI Report
OS-R8714 (1987), §4, p. 7, proof of Theorem 4).

The instance consists of disjoint sets `A = {a_1, …, a_n}`, `B = {b_1, …, b_n}`,
`C = {c_1, …, c_n}` and a family `F = {T_1, …, T_m}` of triples with `|T_i ∩ A| = |T_i ∩ B| =
|T_i ∩ C| = 1`. The elements `a_j`, `b_k`, `c_l` are indexed by `j, k, l : Fin n`, and the triple
`T_i` is `T i = (j, k, l)`, standing for `(a_j, b_k, c_l)`; the triples are indexed by `i : Fin m`,
so the same triple may occur several times in the family.

A matching is a subfamily `F'`, given by its index set `F' : Finset (Fin m)`, with `|F'| = n`
whose union is `A ∪ B ∪ C`: every `a_j`, every `b_k` and every `c_l` lies in some triple of `F'`. -/
def IsThreeDimMatching {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (F' : Finset (Fin m)) :
    Prop :=
  F'.card = n ∧
    (∀ j : Fin n, ∃ i ∈ F', (T i).1 = j) ∧
    (∀ k : Fin n, ∃ i ∈ F', (T i).2.1 = k) ∧
    (∀ l : Fin n, ∃ i ∈ F', (T i).2.2 = l)

/-- The three coordinates of a triple `t = (j, k, l)`: coordinate `0` is the `A`-index `j`,
coordinate `1` the `B`-index `k`, coordinate `2` the `C`-index `l`. -/
def tripleCoord {n : ℕ} (t : Fin n × Fin n × Fin n) : Fin 3 → Fin n :=
  ![t.1, t.2.1, t.2.2]

/-- The element job of the scheduling instance of Theorem 4 corresponding to an element of
`A ∪ B ∪ C`: `thm4ElemJob m c x` is the job of `a_x` if `c = 0`, of `b_x` if `c = 1`, of `c_x`
if `c = 2`. The `3n + (m - n)` jobs are enumerated as `Fin (3 * n + (m - n))`, the `3n` element
jobs first (as `Fin 3 × Fin n ≃ Fin (3 * n)`), then the `m - n` dummy jobs. -/
def thm4ElemJob {n : ℕ} (m : ℕ) (c : Fin 3) (x : Fin n) : Fin (3 * n + (m - n)) :=
  finSumFinEquiv (Sum.inl (finProdFinEquiv (c, x)))

/-- The `k`-th dummy job of the scheduling instance of Theorem 4, `k : Fin (m - n)`. -/
def thm4DummyJob {n m : ℕ} (k : Fin (m - n)) : Fin (3 * n + (m - n)) :=
  finSumFinEquiv (Sum.inr k)

/-- The processing times of the scheduling instance built from a 3-DIMENSIONAL MATCHING instance
`T` in the proof of Theorem 4 (p. 7): `m` machines, machine `i` corresponding to the triple
`T_i = (a_j, b_k, c_l)`; `3n` element jobs and `m - n` dummy jobs. Machine `i` processes each of
the jobs of `a_j`, `b_k`, `c_l` in one time unit and every other job in three time units; the
dummy jobs require three time units on each machine. -/
def thm4Times {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    Matrix (Fin m) (Fin (3 * n + (m - n))) ℕ :=
  fun i j =>
    Sum.elim
      (fun e => if tripleCoord (T i) (finProdFinEquiv.symm e).1 = (finProdFinEquiv.symm e).2
        then 1 else 3)
      (fun _ => 3) (finSumFinEquiv.symm j)

@[simp] theorem thm4Times_elem {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (i : Fin m)
    (c : Fin 3) (x : Fin n) :
    thm4Times T i (thm4ElemJob m c x) = if tripleCoord (T i) c = x then 1 else 3 := by
  simp only [thm4Times, thm4ElemJob, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem thm4Times_dummy {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (i : Fin m)
    (k : Fin (m - n)) : thm4Times T i (thm4DummyJob k) = 3 := by
  simp [thm4Times, thm4DummyJob]

end UnrelatedSched.TwoTimes
