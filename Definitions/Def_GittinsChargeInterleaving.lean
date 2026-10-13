import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Finset.Interval

/-!
Deterministic reward-stack interleavings used in the proof of the Gittins
index theorem.  See Lattimore--Szepesvari, *Bandit Algorithms*, Lemma 35.10
and Exercise 35.9, printed p. 451 (free-online PDF p. 459).
-/

namespace BanditAlgorithm

/-- Number of occurrences of arm `i` strictly before global round `n`. -/
def stackPullCountBefore {k : ℕ} (a : ℕ → Fin k) (i : Fin k) (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range n, if a t = i then 1 else 0

/-- Interleave arm-indexed stacks according to the global action sequence. -/
def chargeStackInterleaving {k : ℕ}
    (H : Fin k → ℕ → ℝ) (a : ℕ → Fin k) (n : ℕ) : ℝ :=
  H (a n) (stackPullCountBefore a (a n) n)

/-- At every round, the selected arm has a maximal currently exposed charge. -/
def IsGreedyChargeStackInterleaving {k : ℕ}
    (H : Fin k → ℕ → ℝ) (a : ℕ → Fin k) : Prop :=
  ∀ n i,
    H i (stackPullCountBefore a i n) ≤
      H (a n) (stackPullCountBefore a (a n) n)

/-- Undiscounted value of taking the first `m i` entries from every stack. -/
def chargeStackAllocationValue {k : ℕ}
    (H : Fin k → ℕ → ℝ) (m : Fin k → ℕ) : ℝ :=
  ∑ i : Fin k, ∑ u ∈ Finset.range (m i), H i u

/-- Remove the exposed head of stack `j`. -/
def advanceChargeStack {k : ℕ}
    (H : Fin k → ℕ → ℝ) (j : Fin k) : Fin k → ℕ → ℝ :=
  fun i u ↦ if i = j then H i (u + 1) else H i u

/-- Remove one allocated entry from arm `i`. -/
def decrementChargeAllocation {k : ℕ}
    (m : Fin k → ℕ) (i : Fin k) : Fin k → ℕ :=
  fun j ↦ if j = i then m j - 1 else m j

end BanditAlgorithm
