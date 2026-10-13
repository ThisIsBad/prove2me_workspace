import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_ThreeHalves_ThreeDimMatching

namespace UnrelatedSched.ThreeHalves

/-- The number `t_j` of triples of type `j`, i.e. of triples `T_i` that contain `a_j`
(Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §4, proof of Theorem 5, p. 7). -/
def typeCount {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => (T i).1 = j)).card

/-- The jobs of the scheduling instance of Theorem 5 (p. 7): one element job for each `b_k`
(`Sum.inl k`), one element job for each `c_l` (`Sum.inr (Sum.inl l)`), and `t_j − 1` dummy jobs of
type `j` for each `j` (`Sum.inr (Sum.inr ⟨j, r⟩)`, `r < t_j − 1`). There are no jobs for the
elements of `A`.

Formalization Note: `t_j − 1` is natural-number subtraction, so a type `j` with `t_j = 0` has no
dummy job (the paper does not treat this case; the instance then has no schedule of makespan
at most `2`, and `T` has no matching). -/
abbrev Job {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) : Type :=
  Fin n ⊕ Fin n ⊕ (Σ j : Fin n, Fin (typeCount T j - 1))

/-- The processing time of a job on machine `i` in the instance of Theorem 5 (pp. 7–8). Machine
`i` corresponds to the triple `T_i = (a_j, b_k, c_l)`; it processes each of the element jobs of
`b_k` and `c_l` in one time unit, each dummy job of type `j` in two time units, and every other
job in three time units. -/
def procTime {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (i : Fin m) : Job T → ℕ
  | Sum.inl k => if (T i).2.1 = k then 1 else 3
  | Sum.inr (Sum.inl l) => if (T i).2.2 = l then 1 else 3
  | Sum.inr (Sum.inr ⟨j, _⟩) => if (T i).1 = j then 2 else 3

/-- The number of jobs of the instance of Theorem 5: `2n + Σ_j (t_j − 1)`. -/
def numJobs {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) : ℕ :=
  Fintype.card (Job T)

/-- A fixed enumeration of the jobs by `Fin (numJobs T)`, so that schedules are maps
`Fin (numJobs T) → Fin m` as in `MatousekLP.Scheduling`. Every statement about this instance
quantifies over all schedules, so it does not depend on which enumeration is chosen. -/
noncomputable def jobEnum {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    Job T ≃ Fin (numJobs T) :=
  Fintype.equivFin (Job T)

/-- The processing-time matrix `p_ij` of the instance of Theorem 5, with machines `Fin m` and the
jobs enumerated by `jobEnum T`. All entries are positive integers, in `{1, 2, 3}`. -/
noncomputable def P {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    Matrix (Fin m) (Fin (numJobs T)) ℕ :=
  fun i r => procTime T i ((jobEnum T).symm r)

end UnrelatedSched.ThreeHalves
