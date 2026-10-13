import Mathlib
import Definitions.Def_UnrelatedSched_FixedMachines_DeadlineLP

namespace UnrelatedSched.FixedMachines

/-- `L` is a *schedule of long assignments* for the instance `(P, d)` and the accuracy `ε`
(§3, p. 6): a partial assignment of jobs to machines (`L j = none` means that job `j` is not
assigned) in which every assignment is long, i.e. `L j = some i` implies `p_ij > ε d`. -/
def IsLongSchedule {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (ε : ℝ) (d : ℕ)
    (L : Fin n → Option (Fin m)) : Prop :=
  ∀ j i, L j = some i → ε * (d : ℝ) < (P i j : ℝ)

/-- The total processing time `t_i` of the long assignments of `L` to machine `i` (§3, p. 6). -/
def longLoad {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (L : Fin n → Option (Fin m))
    (i : Fin m) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => L j = some i), (P i j : ℝ)

/-- A schedule of long assignments is *admissible* for the deadline `d` when no machine's long
assignments exceed the deadline: `t_i ≤ d` for every machine `i`. Every partial schedule of long
assignments contained in a schedule of makespan at most `d` is admissible; the procedure `A_ε`
enumerates the admissible ones (§3, p. 6). -/
def IsAdmissible {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (ε : ℝ) (d : ℕ)
    (L : Fin n → Option (Fin m)) : Prop :=
  IsLongSchedule P ε d L ∧ ∀ i, longLoad P L i ≤ (d : ℝ)

/-- The total processing time of the jobs left unassigned by `L` that the schedule `σ` puts on
machine `i` (the "short assignments" of §3, p. 6). -/
def shortLoad {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (L : Fin n → Option (Fin m))
    (σ : Fin n → Fin m) (i : Fin m) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => L j = none ∧ σ j = i), (P i j : ℝ)

/-- The residual linear program of §3, p. 6: (LP) of the Rounding Theorem for the jobs that `L`
leaves unassigned, `R = {j : L j = none}`, with machine deadlines `d_i = d - t_i` and threshold
`t = ε d`. -/
def ResidualLP {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (ε : ℝ) (d : ℕ)
    (L : Fin n → Option (Fin m)) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  DeadlineLP P {j | L j = none} (fun i => (d : ℝ) - longLoad P L i) (ε * (d : ℝ))

/-- A *vertex selector* models the LP solver used by `A_ε`: for each deadline `d` and each
schedule of long assignments `L`, `V d L` is a vertex (extreme point) of the residual LP when
that LP is feasible, and `V d L = none` only when the residual LP is empty. -/
def IsVertexSelector {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (ε : ℝ)
    (V : ℕ → (Fin n → Option (Fin m)) → Option (Matrix (Fin m) (Fin n) ℝ)) : Prop :=
  ∀ d L, (∀ x, V d L = some x → x ∈ Set.extremePoints ℝ (ResidualLP P ε d L)) ∧
         (V d L = none → ResidualLP P ε d L = ∅)

/-- `D` is the procedure `A_ε` of §3, p. 6, run with the LP solver `V`. For a fixed processing
time matrix `P`, `D d = none` is the answer 'no' and `D d = some σ` is the answer 'almost' with
the schedule `σ`.
1. `D` answers 'no' exactly when the residual LP of every admissible schedule of long
   assignments is empty (the solver returns no vertex).
2. When `D` returns `σ`, there are an admissible `L` and the vertex `x = V d L` such that `σ`
   extends `L` on the long jobs, `σ` assigns every remaining job to a machine in the support of
   `x`, and the remaining jobs form a solution of the integer program (IP) of the Rounding
   Theorem for the residual instance: the short load of machine `i` is at most
   `(d - t_i) + ε d`. -/
def IsAepsProcedure {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (ε : ℝ)
    (V : ℕ → (Fin n → Option (Fin m)) → Option (Matrix (Fin m) (Fin n) ℝ))
    (D : ℕ → Option (Fin n → Fin m)) : Prop :=
  ∀ d : ℕ,
    (D d = none ↔ ∀ L, IsAdmissible P ε d L → V d L = none) ∧
    (∀ σ, D d = some σ →
      ∃ L x, IsAdmissible P ε d L ∧ V d L = some x ∧
        (∀ j i, L j = some i → σ j = i) ∧
        (∀ j, L j = none → 0 < x (σ j) j) ∧
        (∀ i, shortLoad P L σ i ≤ ((d : ℝ) - longLoad P L i) + ε * (d : ℝ)))

end UnrelatedSched.FixedMachines
