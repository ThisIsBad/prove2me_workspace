import Mathlib

namespace SchedComplexity.Shops

/-- A general shop instance with `n` jobs and `m` machines (Brucker, Lenstra & Rinnooy Kan,
Report BW 43/75, Section 3, pp. 6–7). Jobs `J_1, …, J_n` are `Fin n` and machines
`M_1, …, M_m` are `Fin m`, both 0-based (`J_j` is `j - 1`, `M_i` is `i - 1`).

* `ops j` is the sequence of operations of job `J_j`: its `r`-th entry `(μ_jr, p_jr)` says that the
  `r`-th operation runs on machine `μ_jr` for `p_jr` time units. Its length is the number of
  operations `m_j`, and the list of first components is the machine order `μ_j`; a machine may
  occur more than once (e.g. `μ_n = (M_2, M_1, M_2)` in Theorem 4(i)). Processing times are
  nonnegative integers (zero allowed, p. 6).
* `release j` is the release date `r_j ∈ ℕ`.
* `prec` is the set of precedence arcs: `(j, k) ∈ prec` means `J_j < J_k` ("`J_j` precedes `J_k`",
  p. 7). -/
structure ShopInstance (n m : ℕ) where
  ops : Fin n → List (Fin m × ℕ)
  release : Fin n → ℕ
  prec : Finset (Fin n × Fin n)

namespace ShopInstance

variable {n m : ℕ} (I : ShopInstance n m)

/-- The operations of the instance: pairs `⟨j, r⟩` of a job `j` and an index `r` (0-based) into its
operation list. -/
abbrev Op := Σ j : Fin n, Fin (I.ops j).length

/-- The machine of operation `⟨j, r⟩`. -/
def mach (o : I.Op) : Fin m := ((I.ops o.1).get o.2).1

/-- The processing time of operation `⟨j, r⟩`. -/
def proc (o : I.Op) : ℕ := ((I.ops o.1).get o.2).2

/-- The completion time `C_j` of job `j` under start times `S`: the latest completion time
`S(o) + p(o)` of its operations (`0` for a job without operations). Under the job's own chain
constraint this is the completion time of its last operation. -/
def completion (S : I.Op → ℕ) (j : Fin n) : ℕ :=
  Finset.univ.sup (fun r : Fin (I.ops j).length => S ⟨j, r⟩ + I.proc ⟨j, r⟩)

/-- `S` (a start time `S(o) ∈ ℕ` for every operation `o`) is a feasible schedule of the instance
(Section 3, pp. 6–7):

1. no operation of job `j` starts before its release date `r_j`;
2. the operations of a job are processed in the order of its operation list, each starting no
   earlier than the previous one completes;
3. two distinct operations on the same machine (of different jobs, or of the same job) do not
   overlap: one of them completes before the other starts ("each machine can handle at most one
   job at a time");
4. `J_j < J_k` implies `C_j ≤ B_k`: every operation of `J_k` (in particular its first one, which
   starts at `B_k`) starts no earlier than the completion time `C_j` of `J_j`.

**Formalization Note.** Start times are natural numbers: the paper computes start and completion
times from processing orders on integer data (p. 6), every criterion is regular and every side
constraint survives shifting operations to the left, so integer start times lose no schedule
value. Condition 1 is stated for every operation; by condition 2 it is equivalent to the first
operation starting at time `≥ r_j`. -/
def IsFeasible (S : I.Op → ℕ) : Prop :=
  (∀ o : I.Op, I.release o.1 ≤ S o) ∧
  (∀ (j : Fin n) (r r' : Fin (I.ops j).length), r'.val = r.val + 1 →
      S ⟨j, r⟩ + I.proc ⟨j, r⟩ ≤ S ⟨j, r'⟩) ∧
  (∀ o o' : I.Op, o ≠ o' → I.mach o = I.mach o' →
      S o + I.proc o ≤ S o' ∨ S o' + I.proc o' ≤ S o) ∧
  (∀ j k : Fin n, (j, k) ∈ I.prec → ∀ r' : Fin (I.ops k).length, I.completion S j ≤ S ⟨k, r'⟩)

/-- The schedule `S` has makespan `C_max = max_j C_j ≤ y`, stated as `C_j ≤ y` for every job `j`
(no maximum is formed). -/
def CmaxLE (S : I.Op → ℕ) (y : ℕ) : Prop := ∀ j : Fin n, I.completion S j ≤ y

/-- The recognition question of `n|m|ℓ,λ|C_max` (Section 2, p. 4): the instance has a feasible
schedule with value `C_max ≤ y`. -/
def HasScheduleLE (y : ℕ) : Prop := ∃ S : I.Op → ℕ, I.IsFeasible S ∧ I.CmaxLE S y

/-- The precedence graph of the instance is a **branching** (`tree`, p. 7: "a set of directed trees
with either indegree or outdegree at most one for all vertices"): it has no directed cycle (in
particular no loop), and either every vertex has indegree at most one (an out-forest) or every
vertex has outdegree at most one (an in-forest). The "either … or" is read for the whole graph. -/
def IsBranching : Prop :=
  (∀ j : Fin n, ¬ Relation.TransGen (fun a b => (a, b) ∈ I.prec) j j) ∧
  ((∀ k : Fin n, (I.prec.filter (fun e => e.2 = k)).card ≤ 1) ∨
   (∀ j : Fin n, (I.prec.filter (fun e => e.1 = j)).card ≤ 1))

/-- The code of an instance together with a threshold `y`, as a list of natural numbers:
`n`, `m`; then, for each job `j = 1, …, n` in turn, `r_j`, `m_j`, and for each operation the
machine index (0-based) followed by its processing time; then the `n × n` precedence adjacency
matrix row by row (`1` for an arc `J_j < J_k`, `0` otherwise); then `y`. The list determines the
instance and `y` (it can be read from left to right). -/
def code (y : ℕ) : List ℕ :=
  [n, m] ++
  (List.ofFn fun j : Fin n =>
      [I.release j, (I.ops j).length] ++ ((I.ops j).map fun e => [e.1.val, e.2]).flatten).flatten ++
  (List.ofFn fun j : Fin n => List.ofFn fun k : Fin n =>
      if (j, k) ∈ I.prec then 1 else 0).flatten ++
  [y]

end ShopInstance

end SchedComplexity.Shops
