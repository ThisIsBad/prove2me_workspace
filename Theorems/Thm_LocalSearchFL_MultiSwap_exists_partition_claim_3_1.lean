import Mathlib
import Definitions.Def_LocalSearchFL_MultiSwap_capture

namespace LocalSearchFL.MultiSwap

/-- Claim 3.1 (p. 552), in existence form. If `|S| = |O|`, then `S` can be partitioned into
`A_1, …, A_r` and `O` into `B_1, …, B_r` (here `r = m + 1`, `A_i = A (i-1)` and `B_i = B (i-1)`
for `i ≤ m`, and `A_r = Ar`, `B_r = Br`) such that
1. for `1 ≤ i ≤ r − 1`, `|A_i| = |B_i|` and `B_i = capture(A_i)`; and `|A_r| = |B_r|`;
2. for `1 ≤ i ≤ r − 1`, `A_i` has exactly one bad facility;
3. `A_r` contains only good facilities.
Capture, good and bad are taken with respect to the original `S` and `O` (the assignments `σS`,
`σO` and the set `O`). The last blocks `Ar`, `Br` may be empty. -/
theorem exists_partition_claim_3_1 {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O : Finset Fa) (hcard : S.card = O.card) :
    ∃ (m : ℕ) (A B : Fin m → Finset Fa) (Ar Br : Finset Fa),
      -- `A_1, …, A_{r-1}, A_r` partition `S`
      (∀ i, A i ⊆ S) ∧ Ar ⊆ S ∧ (∀ s ∈ S, (∃ i, s ∈ A i) ∨ s ∈ Ar) ∧
      (∀ i i', i ≠ i' → Disjoint (A i) (A i')) ∧ (∀ i, Disjoint (A i) Ar) ∧
      -- `B_1, …, B_{r-1}, B_r` partition `O`
      (∀ i, B i ⊆ O) ∧ Br ⊆ O ∧ (∀ o ∈ O, (∃ i, o ∈ B i) ∨ o ∈ Br) ∧
      (∀ i i', i ≠ i' → Disjoint (B i) (B i')) ∧ (∀ i, Disjoint (B i) Br) ∧
      -- property 1
      (∀ i, (A i).card = (B i).card ∧ B i = capture σS σO O (A i)) ∧ Ar.card = Br.card ∧
      -- property 2
      (∀ i, ∃ b ∈ A i, ¬ IsGood σS σO O b ∧ ∀ s ∈ A i, s ≠ b → IsGood σS σO O s) ∧
      -- property 3
      (∀ s ∈ Ar, IsGood σS σO O s) := by sorry

end LocalSearchFL.MultiSwap

