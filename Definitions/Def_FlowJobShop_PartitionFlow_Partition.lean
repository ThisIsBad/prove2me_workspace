import Mathlib

namespace FlowJobShop.PartitionFlow

/-- PARTITION (Gonzalez–Sahni 1978, p. 37): the multiset `S = {a_1, …, a_n}` of nonnegative
integers, given as `a : Fin n → ℕ` (indices 0-based), **has a partition** if there is a subset
`u` of the indices with `∑_{i ∈ u} a_i = (∑_i a_i)/2`, written here without division as
`2 · ∑_{i ∈ u} a_i = ∑_i a_i`. -/
def HasPartition {n : ℕ} (a : Fin n → ℕ) : Prop :=
  ∃ u : Finset (Fin n), 2 * ∑ i ∈ u, a i = ∑ i, a i

end FlowJobShop.PartitionFlow
