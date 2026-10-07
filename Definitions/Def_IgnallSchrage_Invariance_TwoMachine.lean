import Mathlib
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2
import Definitions.Def_IgnallSchrage_Invariance_Node

namespace IgnallSchrage.Invariance

noncomputable section

/-- One more job on two machines: from `(A, d, D)` — the time machine A finishes, the time
machine B finishes (the completion time `d_k` of the last job), and the sum of the completion
times so far — and job `i`: machine A finishes at `A + a i`, job `i` completes on machine B at
`d_i = max d (A + a i) + b i`, and the sum becomes `D + d_i`. -/
def appendJob2 {n : ℕ} (a b : Fin n → ℝ) (t : ℝ × ℝ × ℝ) (i : Fin n) : ℝ × ℝ × ℝ :=
  let d₁ := t.1 + a i
  let d₂ := max t.2.1 d₁ + b i
  (d₁, d₂, t.2.2 + d₂)

/-- `state2 a b J = (Σ_{j∈J_r} a_j, d_k, Σ_{i∈J_r} d_i)` for a node `J = J_r` of the
two-machine problem (pp. 405–406), its jobs processed in the order of `J` as early as possible
from time `0`: the time machine A finishes `J_r`, the completion time on machine B of the last
job `k` of `J_r`, and the sum of the completion times `d_i` (on machine B) of the jobs of `J_r`.
At the root `J = []` it is `(0, 0, 0)`; the root has no last job `k`, and its value `d_k = 0`
is a convention (the procedure never ranks the root). Whenever `J` is the list of the first `r`
positions of an order `σ`, the `d_i` computed here are Johnson's
`JohnsonFlowShop.TwoStage.asapC2 a b σ (p + 1)`, `p < r`. -/
def state2 {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) : ℝ × ℝ × ℝ :=
  J.foldl (appendJob2 a b) (0, 0, 0)

/-- `T_r` of p. 405 for the node `J = J_r` and an ordering `l = (i_1, …, i_{n-r})` of `J̄_r`:
`T_r = Σ_{p=1}^{n-r} [ Σ_{j∈J_r} a_j + (n-r-p+1) a_{i_p} + b_{i_p} ]`.
With the 0-based position `p` of `l` the coefficient `n-r-(p+1)+1` is `l.length - p`
(natural subtraction with `p < l.length`, so no truncation). -/
def Tval {n : ℕ} (a b : Fin n → ℝ) (J l : List (Fin n)) : ℝ :=
  ∑ p : Fin l.length,
    ((state2 a b J).1 + ((l.length - p.val : ℕ) : ℝ) * a l[p] + b l[p])

/-- `S_r` of p. 405 for the node `J = J_r` and an ordering `l = (j_1, …, j_{n-r})` of `J̄_r`:
`S_r = Σ_{p=1}^{n-r} [ max(d_k, Σ_{j∈J_r} a_j + min_{i∈J̄_r} a_i) + (n-r-p+1) b_{j_p} ]`,
`k` the last job of `J_r`. -/
def Sval {n : ℕ} (a b : Fin n → ℝ) (J l : List (Fin n)) : ℝ :=
  ∑ p : Fin l.length,
    (max (state2 a b J).2.1 ((state2 a b J).1 + IgnallSchrage.Makespan.minOver (IgnallSchrage.Makespan.unscheduled J) a) +
      ((l.length - p.val : ℕ) : ℝ) * b l[p])

/-- The orderings of `J̄_r`: all arrangements, as lists without repetition, of the jobs not
scheduled in `J`. This finite set is nonempty (it contains one listing of `J̄_r`). -/
def orderings {n : ℕ} (J : List (Fin n)) : Finset (List (Fin n)) :=
  ((IgnallSchrage.Makespan.unscheduled J).toList.permutations).toFinset

theorem orderings_nonempty {n : ℕ} (J : List (Fin n)) : (orderings J).Nonempty :=
  ⟨(IgnallSchrage.Makespan.unscheduled J).toList, List.mem_toFinset.2 (List.mem_permutations.2 (List.Perm.refl _))⟩

/-- `T̂_r` (p. 406): "the minimum possible value for `T_r`", the minimum of `T_r` over all
orderings of `J̄_r`. -/
def That {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  (orderings J).inf' (orderings_nonempty J) (Tval a b J)

/-- `Ŝ_r` (p. 406): the minimum value of `S_r` over all orderings of `J̄_r`. -/
def Shat {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  (orderings J).inf' (orderings_nonempty J) (Sval a b J)

/-- The two-machine lower bound of p. 406 of a node `J = J_r`:
`LB(J_r) = Σ_{i∈J_r} d_i + max(T̂_r, Ŝ_r)`. It is meant for nodes with `1 ≤ r ≤ n - 1`; at the
root its value uses the convention `d_k = 0` and is never used by the procedure. -/
def lowerBound2 {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  (state2 a b J).2.2 + max (That a b J) (Shat a b J)

/-- The sum of the completion times on machine B of a full sequence `σ` (`σ k` = job in position
`k`), `Σ_i d_i`, under Johnson's as-soon-as-possible two-machine schedule: the job in position
`k` completes at `asapC2 a b σ (k + 1)`. The paper minimizes the mean completion time, which is
this sum divided by `n`. -/
def sumCompletion {n : ℕ} (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ k : Fin n, JohnsonFlowShop.TwoStage.asapC2 a b σ (k.val + 1)

end

end IgnallSchrage.Invariance
