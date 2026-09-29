import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_problem

namespace BiconvexProg.BranchBound

variable {n : ℕ}

open Classical in
/-- An (infinite) run of the convex-envelope branch-and-bound algorithm (pp. 276–279) on the data
`S, f, g, Ω`. Stages are numbered from `0` (the paper's stage `k + 1` is index `k`).
* `nodes k` : the multiset of open nodes (boxes) at stage `k`; stage `0` is `{Ω}`;
* `sel k` : the open node selected for branching at stage `k`;
* `pt k` : the stage point `(xᵏ, yᵏ)`, a solution of the selected node's subproblem
  `min {ψ^{sel k} : S ∩ sel k}`, whose value is least among all open nodes' subproblem
  values (Best Bound Rule); equivalently `ψ^{sel k}(pt k) ≤ ψ^B(z)` for every open `B` and every
  `z ∈ S ∩ B`;
* `idx k` : the branching index, maximising `x_i y_i − Vex_{(sel k)_i} x_i y_i` at `pt k`;
* the next stage removes `sel k` and adds its four children split at `idx k` and at the
  `idx k`-th coordinate pair of `pt k` (Figure 1).
Runs never stop (the stopping test `v_b = V_b` is ignored) and the optional pruning of p. 278 is
omitted. -/
structure IsRun (S : Set ((Fin n → ℝ) × (Fin n → ℝ))) (f g : (Fin n → ℝ) → ℝ) (Ω : Box n)
    (nodes : ℕ → Multiset (Box n)) (sel : ℕ → Box n) (idx : ℕ → Fin n)
    (pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)) : Prop where
  init : nodes 0 = {Ω}
  sel_mem : ∀ k, sel k ∈ nodes k
  pt_mem : ∀ k, pt k ∈ S ∩ (sel k).toSet
  best_bound : ∀ k, ∀ B ∈ nodes k, ∀ z ∈ S ∩ B.toSet, nodeFun f g (sel k) (pt k) ≤ nodeFun f g B z
  idx_max : ∀ k i, gap (sel k) i (pt k) ≤ gap (sel k) (idx k) (pt k)
  step : ∀ k, nodes (k + 1) =
    (nodes k).erase (sel k) + (sel k).split (idx k) ((pt k).1 (idx k)) ((pt k).2 (idx k))

/-- The best lower bound `v_bᵏ` at stage `k` (p. 279): the value `ψ^{sel k}(xᵏ, yᵏ)` of the
selected node, which by the Best Bound Rule is the least subproblem value among open nodes. -/
noncomputable def bestLower (f g : (Fin n → ℝ) → ℝ) (sel : ℕ → Box n)
    (pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)) (k : ℕ) : ℝ :=
  nodeFun f g (sel k) (pt k)

/-- The best upper bound `V_bᵏ = min {φ(xˡ, yˡ) : l ≤ k}` at stage `k` (p. 279, defining
formula; stages from `0`). -/
noncomputable def bestUpper (f g : (Fin n → ℝ) → ℝ) (pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ))
    (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).inf' ⟨0, by simp⟩ (fun l => objective f g (pt l))

/-- The stage function `ψᵏ` built from the open nodes `N` (pp. 276, 279): at a point `z`, the
least node value `ψ^B(z)` over the open boxes `B ∈ N` containing `z`. Where only one open box
contains `z` this is the paper's `ψᵏ(z) = ψ^{kj}(z)`; on shared faces the node values need not
agree, and the minimum is taken. Junk value: `0` at points lying in no open box
(real `sInf ∅`). -/
noncomputable def stageFun (f g : (Fin n → ℝ) → ℝ) (N : Multiset (Box n))
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  sInf ((fun B => nodeFun f g B z) '' {B | B ∈ N ∧ z ∈ B.toSet})

end BiconvexProg.BranchBound
