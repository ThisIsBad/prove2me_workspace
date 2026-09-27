import Mathlib

namespace ComplexScheduling

variable {n r : ℕ}

/-- A schedule satisfies the **disjunctions** `i − j` listed in `D` (as pairs `(i, j)`, the order
being immaterial) when for each of them either `i → j` or `j → i` holds, that is, the two
activities are not processed in parallel.  Brucker and Knust, *Complex Scheduling*, §3.6.1,
p. 162: a disjunction is the negation of the parallelity relation (3.110). -/
def SatisfiesDisjunctions (p : Fin n → ℕ) (D : Finset (Fin n × Fin n)) (S : Fin n → ℕ) : Prop :=
  ∀ e ∈ D, S e.1 + p e.1 ≤ S e.2 ∨ S e.2 + p e.2 ≤ S e.1

/-- A **disjunctive set** for the conjunction set `C` and the disjunction set `D`: a set `I` of at
least two activities such that any two distinct members are related by a disjunction `i − j ∈ D`
or a conjunction `i → j ∈ C` or `j → i ∈ C`.  Brucker and Knust §3.6.4, p. 168. -/
def IsDisjunctiveSet (C D : Finset (Fin n × Fin n)) (I : Finset (Fin n)) : Prop :=
  2 ≤ I.card ∧
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (i, j) ∈ D ∨ (j, i) ∈ D ∨ (i, j) ∈ C ∨ (j, i) ∈ C

/-- A schedule respects the **time windows** `[r_i, d_i]`: every activity starts no earlier than
its head `r_i` and completes no later than its deadline `d_i`.  Brucker and Knust §3.6.4,
p. 169. -/
def WithinWindows (rel dl p : Fin n → ℕ) (S : Fin n → ℕ) : Prop :=
  ∀ i, rel i ≤ S i ∧ S i + p i ≤ dl i

/-- The **total processing time** `P(J) := ∑_{i ∈ J} p_i` of a set of activities.  Brucker and
Knust §3.6.4, p. 169. -/
def totalProcessing (p : Fin n → ℕ) (J : Finset (Fin n)) : ℕ := ∑ i ∈ J, p i

/-- Activity `i` **starts first** in the set `J` under the schedule `S`: it belongs to `J` and no
activity of `J` starts earlier.  Brucker and Knust §3.6.4, p. 169. -/
def StartsFirstIn (S : Fin n → ℕ) (J : Finset (Fin n)) (i : Fin n) : Prop :=
  i ∈ J ∧ ∀ j ∈ J, S i ≤ S j

/-- Activity `i` **ends last** in the set `J` under the schedule `S`: it belongs to `J` and no
activity of `J` completes later.  Brucker and Knust §3.6.4, p. 169. -/
def EndsLastIn (p S : Fin n → ℕ) (J : Finset (Fin n)) (i : Fin n) : Prop :=
  i ∈ J ∧ ∀ j ∈ J, S j + p j ≤ S i + p i

/-- The **work** `W(J) := ∑_{i ∈ J} r_{ik} p_i` that the activities of `J` need from the
cumulative resource `k`, where `w_i := r_{ik} p_i`.  Brucker and Knust §3.6.5, p. 186. -/
def totalWork (p : Fin n → ℕ) (demand : Fin n → Fin r → ℕ) (k : Fin r) (J : Finset (Fin n)) : ℕ :=
  ∑ i ∈ J, demand i k * p i

end ComplexScheduling
