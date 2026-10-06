import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_ValueDist
import Definitions.Def_CHMSPricing_OpmUniform_SetSystem

namespace CHMSPricing.OpmUniform

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The agents who "desire" service at prices `p` given values `v`: those with `vᵢ ≥ pᵢ`. -/
noncomputable def desiring (p v : ι → ℝ) : Finset ι :=
  open Classical in Finset.univ.filter (fun i => p i ≤ v i)

/-- §2.2, p. 4: `S ∈ 𝒮_v`, i.e. `S` is a maximal feasible subset of agents that desire service
given values `v` and prices `p`: (1) `S ∈ 𝒥`, (2) `vᵢ ≥ pᵢ` for all `i ∈ S`, and (3) every
feasible (strict) superset `S'` of `S` contains some agent `i` with `vᵢ < pᵢ`. -/
def IsMaxFeasDesiring (J : SetSystem ι) (p v : ι → ℝ) (S : Finset ι) : Prop :=
  J.Feasible S ∧ (∀ i ∈ S, p i ≤ v i) ∧
    ∀ S' : Finset ι, S ⊂ S' → J.Feasible S' → ∃ i ∈ S', v i < p i

open Classical in
/-- The finite class `𝒮_v` of maximal feasible desiring sets. -/
noncomputable def maxFeasDesiringSets (J : SetSystem ι) (p v : ι → ℝ) : Finset (Finset ι) :=
  Finset.univ.filter (IsMaxFeasDesiring J p v)

/-- `𝒮_v` is nonempty: a largest feasible subset of the desiring agents is maximal. -/
theorem maxFeasDesiringSets_nonempty (J : SetSystem ι) (p v : ι → ℝ) :
    (maxFeasDesiringSets J p v).Nonempty := by
  classical
  have hne : ((desiring p v).powerset.filter J.Feasible).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, J.feasible_empty⟩⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  refine ⟨S, ?_⟩
  unfold maxFeasDesiringSets
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hS.2, fun i hi => ?_, fun S' hSS' hS' => ?_⟩
  · have := hS.1 hi
    simpa [desiring] using this
  · by_contra h
    push Not at h
    have hsub : S' ⊆ desiring p v := fun i hi => by simpa [desiring] using h i hi
    have := hmax S' (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hsub, hS'⟩)
    exact absurd (Finset.card_lt_card hSS') (not_lt.2 this)

/-- §2.2, p. 4: the order-oblivious revenue estimate
`ℛ^obl_p = 𝔼_{v∼F} min_{S ∈ 𝒮_v} ∑_{i ∈ S} pᵢ`. -/
noncomputable def oblRevenue (D : ι → ValueDist) (J : SetSystem ι) (p : ι → ℝ) : ℝ :=
  ∫ v, (maxFeasDesiringSets J p v).inf' (maxFeasDesiringSets_nonempty J p v)
    (fun S => ∑ i ∈ S, p i) ∂(prior D)

end CHMSPricing.OpmUniform
