import Mathlib

namespace CHMSPricing.SpmMatroid

/-- A downward-closed set system `𝒥 ⊆ 2^α` (the feasibility constraint of §2.1, p. 4):
the empty set is feasible and every subset of a feasible set is feasible. -/
structure SetSystem (α : Type*) [Fintype α] [DecidableEq α] where
  Feasible : Finset α → Prop
  feasible_empty : Feasible ∅
  feasible_mono : ∀ ⦃A B : Finset α⦄, A ⊆ B → Feasible B → Feasible A

namespace SetSystem

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- §4.1, p. 6: the set system is a matroid. Heredity is `feasible_mono`; this is the
augmentation axiom: for feasible `A, B` with `|A| > |B|` some `e ∈ A \ B` has `B ∪ {e}`
feasible. -/
def IsMatroid (J : SetSystem α) : Prop :=
  ∀ A B : Finset α, J.Feasible A → J.Feasible B → B.card < A.card →
    ∃ e ∈ A \ B, J.Feasible (insert e B)

open Classical in
/-- §4, p. 6: `rank(S) = max_{S' ⊆ S, S' ∈ 𝒥} |S'|`, the size of a largest feasible subset of `S`
(a genuine maximum: `∅` is a feasible subset of every `S`). -/
noncomputable def rank (J : SetSystem α) (S : Finset α) : ℕ :=
  (S.powerset.filter J.Feasible).sup Finset.card

end SetSystem

end CHMSPricing.SpmMatroid
