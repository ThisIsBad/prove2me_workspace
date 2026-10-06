import Mathlib

namespace CHMSPricing.SpmPartition

/-- A downward-closed set system `𝒥 ⊆ 2^α` (the feasibility constraint of §2.1, p. 4):
the empty set is feasible and every subset of a feasible set is feasible. -/
structure SetSystem (α : Type*) [Fintype α] [DecidableEq α] where
  Feasible : Finset α → Prop
  feasible_empty : Feasible ∅
  feasible_mono : ∀ ⦃A B : Finset α⦄, A ⊆ B → Feasible B → Feasible A

namespace SetSystem

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in
/-- §4, p. 6: `rank(S) = max_{S' ⊆ S, S' ∈ 𝒥} |S'|`, the size of a largest feasible subset of `S`
(a genuine maximum: `∅` is a feasible subset of every `S`). -/
noncomputable def rank (J : SetSystem α) (S : Finset α) : ℕ :=
  (S.powerset.filter J.Feasible).sup Finset.card

end SetSystem

/-- §4.2, p. 7: the `k`-uniform matroid on `α`: a set is feasible iff it has at most `k`
elements. -/
def uniformSystem (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) : SetSystem α where
  Feasible S := S.card ≤ k
  feasible_empty := by simp
  feasible_mono := fun _ _ hAB hB => (Finset.card_le_card hAB).trans hB

/-- §4.2, p. 7: the partition matroid ("disjoint union of uniform matroids") given by a map
`part : α → β` assigning each agent to a part and capacities `cap : β → ℕ`: a set is feasible
iff it contains at most `cap b` agents of each part `b`. -/
def partitionSystem {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (part : α → β) (cap : β → ℕ) : SetSystem α where
  Feasible S := ∀ b, (S.filter (fun i => part i = b)).card ≤ cap b
  feasible_empty := by simp
  feasible_mono := fun _ _ hAB hB b =>
    (Finset.card_le_card (Finset.filter_subset_filter _ hAB)).trans (hB b)

end CHMSPricing.SpmPartition
