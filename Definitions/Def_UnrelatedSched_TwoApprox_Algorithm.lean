import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace UnrelatedSched.TwoApprox

open MatousekLP.Scheduling

/-- The load of machine `i` under `σ`, computed in `ℕ`: `∑_{j : σ(j) = i} p_ij`. -/
def natLoad {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (σ : Fin n → Fin m) (i : Fin m) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => σ j = i), P i j

/-- The makespan of `σ` computed in `ℕ`, the largest machine load (`0` when `m = 0`). Its cast to `ℝ`
is the published `makespan (realTimes P) σ`. The binary search compares and bounds makespans with it,
because all of them are integers. -/
def natMakespan {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (σ : Fin n → Fin m) : ℕ :=
  Finset.univ.sup fun i => natLoad P σ i

/-- A machine on which job `j` runs fastest, i.e. minimizing `p_ij` over `i`; ties are broken by the
smallest machine index. Needs `m > 0`. -/
noncomputable def fastestMachine {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (hm : 0 < m)
    (j : Fin n) : Fin m :=
  (Finset.univ.filter fun i => ∀ i', P i j ≤ P i' j).min' (by
    obtain ⟨i, -, hi⟩ :=
      Finset.univ.exists_min_image (fun i => P i j) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    exact ⟨i, by simpa using hi⟩)

/-- The greedy schedule of the proof of Lemma 1 (p. 5): each job is assigned to the machine on which
it runs fastest. -/
noncomputable def greedySchedule {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (hm : 0 < m) :
    Fin n → Fin m :=
  fastestMachine P hm

/-- A decision procedure for a fixed matrix `P`: on deadline `d` it answers `none` ('no') or
`some σ` ('almost', together with the schedule `σ`). -/
abbrev DecisionProcedure (m n : ℕ) : Type := ℕ → Option (Fin n → Fin m)

/-- A `ρ`-relaxed decision procedure (§3, p. 5): on input `(P, d)`, (1) it either outputs 'no' or
produces a schedule with makespan at most `ρ d`, and (2) if the output is 'no', then there is no
schedule with makespan at most `d`. -/
def IsRelaxedDecisionProcedure {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (ρ : ℝ)
    (D : DecisionProcedure m n) : Prop :=
  ∀ d : ℕ, (∀ σ, D d = some σ → makespan (realTimes P) σ ≤ ρ * d) ∧
    (D d = none → ∀ τ : Fin n → Fin m, (d : ℝ) < makespan (realTimes P) τ)

/-- The main loop of the binary search of Lemma 1 (p. 5), on lower bound `l`, upper bound `u` and the
best schedule `best` found so far. While `l < u` it sets `d = ⌊(u + l)/2⌋` and queries `D d`: on
'almost' with `σ` it resets `u` to `d` and keeps whichever of `σ` and `best` has the smaller makespan
(the earlier one on a tie); on 'no' it resets `l` to `d + 1`. When `l ≥ u` it outputs `best`. -/
noncomputable def searchLoop {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (D : DecisionProcedure m n)
    (l u : ℕ) (best : Fin n → Fin m) : Fin n → Fin m :=
  if _h : l < u then
    match D ((u + l) / 2) with
    | some σ =>
        searchLoop P D l ((u + l) / 2)
          (if natMakespan P σ < natMakespan P best then σ else best)
    | none => searchLoop P D ((u + l) / 2 + 1) u best
  else best
termination_by u - l
decreasing_by all_goals omega

/-- The ρ-approximation algorithm of Lemma 1 (p. 5) built from a decision procedure `D`. It starts
from the greedy schedule, whose makespan `t` is the initial upper bound `u`; the initial lower bound
is `⌈t/m⌉` (the paper's `t/m`, rounded up because every makespan is an integer). It then runs the
binary search `searchLoop` and outputs the best schedule found, the greedy one included. -/
noncomputable def binarySearch {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (hm : 0 < m)
    (D : DecisionProcedure m n) : Fin n → Fin m :=
  let g := greedySchedule P hm
  let u₀ := natMakespan P g
  searchLoop P D ⌈(u₀ : ℚ) / m⌉₊ u₀ g

/-- A vertex selector for `P`: for each deadline `d`, it returns a vertex of (LP) with
`d_1 = ⋯ = d_m = t = d` if that LP is feasible, and `none` exactly when it is infeasible. It models
the LP solver of §3 (p. 5), whose choice of vertex the analysis does not control. -/
def IsVertexSelector {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) : Prop :=
  ∀ d : ℕ, (∀ x, V d = some x → IsLPVertex P (fun _ => (d : ℝ)) d x) ∧
    (V d = none → LPPolytope P (fun _ => (d : ℝ)) d = ∅)

/-- `D` is the decision procedure of §3 (pp. 5–6) driven by the vertex selector `V`: on deadline `d`
it answers 'no' exactly when (LP) with `d_1 = ⋯ = d_m = t = d` has no vertex, and otherwise it answers
'almost' with a rounding of the chosen vertex `x̃ = V d`, i.e. a 0-1 solution of (IP) (loads at most
`d + d`) supported on `x̃`. -/
def IsLPRoundingProcedure {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) (D : DecisionProcedure m n) : Prop :=
  ∀ d : ℕ, (D d = none ↔ V d = none) ∧
    ∀ σ, D d = some σ → ∃ x, V d = some x ∧ SupportedOn x σ ∧
      IPFeasible P (fun _ => (d : ℝ)) d σ

end UnrelatedSched.TwoApprox
