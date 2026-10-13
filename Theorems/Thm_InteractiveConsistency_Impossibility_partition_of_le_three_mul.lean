import Mathlib

namespace InteractiveConsistency.Impossibility

/-- Pease, Shostak & Lamport (1980), Section 4, proof of the THEOREM, p. 232: since `3 ≤ n ≤ 3m`
(`n = |P|`), `P` can be partitioned into three nonempty sets `A`, `B`, `C`, each of which has no
more than `m` members. -/
theorem partition_of_le_three_mul {α : Type*} [DecidableEq α] (P : Finset α) (m : ℕ)
    (h3 : 3 ≤ P.card) (hn : P.card ≤ 3 * m) :
    ∃ A B C : Finset α,
      A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      A ∪ B ∪ C = P ∧
      A.card ≤ m ∧ B.card ≤ m ∧ C.card ≤ m := by sorry

end InteractiveConsistency.Impossibility

