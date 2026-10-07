import Mathlib

namespace IgnallSchrage.Makespan

noncomputable section

/-- A node of the tree is terminal when it has scheduled `n - 1` of the `n` jobs: its last job
is then forced, and its sequence is the node followed by the one unscheduled job. -/
def IsTerminal {n : ℕ} (P : List (Fin n)) : Prop :=
  P.length + 1 = n

instance {n : ℕ} (P : List (Fin n)) : Decidable (IsTerminal P) :=
  inferInstanceAs (Decidable (P.length + 1 = n))

/-- The children of node `P`: one node `P ++ [j]` for every job `j` not yet scheduled in `P`,
in increasing job index `j`. -/
def children {n : ℕ} (P : List (Fin n)) : List (List (Fin n)) :=
  ((List.finRange n).filter (fun j => decide (j ∉ P))).map (fun j => P ++ [j])

/-- Insert node `x` into a list ranked by the bound `LB`: `x` goes at the first position whose
node `y` has `LB x ≤ LB y`, i.e. before every node with a bound equal to its own (the tie rule
of p. 403: a newly created node is put before an old node with the same lower bound). -/
def insertNode {n : ℕ} (LB : List (Fin n) → ℝ) (x : List (Fin n)) :
    List (List (Fin n)) → List (List (Fin n))
  | [] => [x]
  | y :: ys => if LB x ≤ LB y then x :: y :: ys else y :: insertNode LB x ys

/-- One step of the branch-and-bound procedure of p. 402 with bound `LB`. If the list is empty
or its first node is terminal (`IsTerminal`), nothing changes (the procedure has stopped).
Otherwise (1) the first node `P` is removed, (2) its children are created, and (3) they are
inserted ranked into the rest of the list one at a time, in increasing index of the attached job,
each by `insertNode`. -/
def step {n : ℕ} (LB : List (Fin n) → ℝ) : List (List (Fin n)) → List (List (Fin n))
  | [] => []
  | P :: rest =>
    if IsTerminal P then P :: rest
    else (children P).foldl (fun L x => insertNode LB x L) rest

/-- The list after `k` steps of the procedure, starting from the list holding only the root
node `[]` (no job scheduled). The procedure stops the first time the first node of the list is
terminal; after that `step` leaves the list unchanged. -/
def run {n : ℕ} (LB : List (Fin n) → ℝ) (k : ℕ) : List (List (Fin n)) :=
  (step LB)^[k] [[]]

/-- The number of nodes created in the first `k` steps: the root, plus the children formed by
every step whose first node is non-terminal. -/
def createdCount {n : ℕ} (LB : List (Fin n) → ℝ) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
    createdCount LB k +
      match run LB k with
      | [] => 0
      | P :: _ => if IsTerminal P then 0 else (children P).length

end

end IgnallSchrage.Makespan
