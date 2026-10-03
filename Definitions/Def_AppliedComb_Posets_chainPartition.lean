import Mathlib

namespace AppliedComb.Posets

/-- A partition of the ground set `X = α` into `k` chains `C i`, `i : Fin k`
(Keller & Trotter, p. 122, Theorem 6.17): every part is a chain, distinct parts are
disjoint, and every point lies in some part. Empty parts are not excluded. -/
def IsChainPartition {α : Type*} [PartialOrder α] {k : ℕ} (C : Fin k → Finset α) : Prop :=
  (∀ i, IsChain (· ≤ ·) (C i : Set α)) ∧
  (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
  (∀ x : α, ∃ i, x ∈ C i)

/-- A partition of the ground set `X = α` into `k` antichains `A i`, `i : Fin k`
(Keller & Trotter, p. 122, Theorem 6.18): every part is an antichain, distinct parts are
disjoint, and every point lies in some part. Empty parts are not excluded. -/
def IsAntichainPartition {α : Type*} [PartialOrder α] {k : ℕ} (A : Fin k → Finset α) : Prop :=
  (∀ i, IsAntichain (· ≤ ·) (A i : Set α)) ∧
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
  (∀ x : α, ∃ i, x ∈ A i)

end AppliedComb.Posets
