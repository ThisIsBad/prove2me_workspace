import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope

open ProcessingNetworks.BackPressure in
theorem solution : ¬ (∀ {I J K : ℕ} (dat : SPNPlanningData I J K)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (nhat : Fin J → ℕ) (zhat : Fin I → ℕ),
    ∃ β ∈ ExtremeAllocations dat, BPFeasible dat nhat zhat β ∧
      ∀ β', BPFeasible dat nhat zhat β' →
        p dat β' (fun i => (zhat i : ℝ)) ≤ p dat β (fun i => (zhat i : ℝ))) := by
  intro h
  let dat : SPNPlanningData 1 1 1 :=
    { B := 1, Γ := 0, m := fun _ => 1, hm := fun _ => one_pos, A := 1, b := fun _ => 1,
      hb := fun _ => one_pos }
  obtain ⟨β, -, ⟨-, hB⟩, -⟩ := h dat (fun k j => by fin_cases k; fin_cases j; simp [dat])
    (fun j => ⟨0, by fin_cases j; exact one_pos⟩) (fun _ => 1) (fun _ => 0)
  have := hB 0
  have hu : 0 ≤ serviceInitiation (fun _ => 1) β 0 := by
    unfold serviceInitiation; split_ifs <;> norm_num
  simp [dat, Matrix.mulVec, dotProduct] at this
  linarith

#print axioms solution
