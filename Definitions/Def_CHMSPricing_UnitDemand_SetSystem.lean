import Mathlib

namespace CHMSPricing.UnitDemand

/-- A downward-closed set system `𝒥 ⊆ 2^α` (the feasibility constraint of §2.1, p. 4):
the empty set is feasible and every subset of a feasible set is feasible. -/
structure SetSystem (α : Type*) [Fintype α] [DecidableEq α] where
  Feasible : Finset α → Prop
  feasible_empty : Feasible ∅
  feasible_mono : ∀ ⦃A B : Finset α⦄, A ⊆ B → Feasible B → Feasible A

namespace SetSystem

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The intersection of two set systems: a set is feasible iff it is feasible in both. -/
def inter (J₁ J₂ : SetSystem α) : SetSystem α where
  Feasible S := J₁.Feasible S ∧ J₂.Feasible S
  feasible_empty := ⟨J₁.feasible_empty, J₂.feasible_empty⟩
  feasible_mono := fun _ _ h hB => ⟨J₁.feasible_mono h hB.1, J₂.feasible_mono h hB.2⟩

end SetSystem

/-- A partition matroid (§4.2, p. 7: "disjoint unions of uniform matroids"): the ground set is
partitioned into the parts `{x | part x = b}`, and a set is feasible iff it contains at most
`cap b` elements of part `b`, for every `b`. -/
def partitionSystem {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (part : α → β) (cap : β → ℕ) : SetSystem α where
  Feasible S := ∀ b, (S.filter (fun x => part x = b)).card ≤ cap b
  feasible_empty := fun b => by simp
  feasible_mono := fun _ _ h hB b =>
    le_trans (Finset.card_le_card (Finset.filter_subset_filter _ h)) (hB b)

/-- The intersection of two partition matroids (§5.3, p. 9). -/
def twoPartitionSystem {α β₁ β₂ : Type*} [Fintype α] [DecidableEq α] [DecidableEq β₁]
    [DecidableEq β₂] (part₁ : α → β₁) (cap₁ : β₁ → ℕ) (part₂ : α → β₂) (cap₂ : β₂ → ℕ) :
    SetSystem α :=
  (partitionSystem part₁ cap₁).inter (partitionSystem part₂ cap₂)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The agents that "desire" service at prices `p` and values `v` (§2.2, p. 4): `pᵢ ≤ vᵢ`. -/
noncomputable def desiring (p v : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => p i ≤ v i)

/-- `S ∈ 𝒮_v` (§2.2, p. 4): `S` is a maximal feasible set of desiring agents, i.e. (1) `S ∈ 𝒥`,
(2) every agent of `S` desires service, (3) no further desiring agent can be added to `S`
feasibly. (By downward closure (3) is equivalent to the paper's "every feasible superset of `S`
contains some agent with `vᵢ < pᵢ`".) -/
def IsMaxFeasDesiring (J : SetSystem ι) (p v : ι → ℝ) (S : Finset ι) : Prop :=
  S ⊆ desiring p v ∧ J.Feasible S ∧
    ∀ i ∈ desiring p v, i ∉ S → ¬ J.Feasible (insert i S)

open Classical in
/-- The finite class `𝒮_v` of maximal feasible desiring sets. -/
noncomputable def maxFeasDesiringSets (J : SetSystem ι) (p v : ι → ℝ) : Finset (Finset ι) :=
  (desiring p v).powerset.filter (IsMaxFeasDesiring J p v)

open Classical in
/-- `𝒮_v` is nonempty: a feasible subset of the desiring agents of maximum cardinality exists
(`∅` is feasible) and is maximal. -/
theorem maxFeasDesiringSets_nonempty (J : SetSystem ι) (p v : ι → ℝ) :
    (maxFeasDesiringSets J p v).Nonempty := by
  have hne : ((desiring p v).powerset.filter J.Feasible).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, J.feasible_empty⟩⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  refine ⟨S, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hS.1, hS.1, hS.2, ?_⟩⟩
  intro i hi hiS hfeas
  have hmem : insert i S ∈ (desiring p v).powerset.filter J.Feasible :=
    Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.insert_subset hi hS.1), hfeas⟩
  have := hmax _ hmem
  rw [Finset.card_insert_of_notMem hiS] at this
  omega

end CHMSPricing.UnitDemand
