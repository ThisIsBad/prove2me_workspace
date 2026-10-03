import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_FeasibleFlowMSFP1
import Definitions.Def_DiscreteConvex_NetworkFlows_DeltaPlus
import Definitions.Def_DiscreteConvex_NetworkFlows_DeltaMinus
import Definitions.Def_DiscreteConvex_NetworkFlows_UpperCapOf
import Definitions.Def_DiscreteConvex_NetworkFlows_NegLowerCapOf
import Definitions.Def_DiscreteConvex_NetworkFlows_Submodular
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerUpper
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerLower

open DiscreteConvex.NetworkFlows

/-- A single self-loop on a single vertex has no arc in any cut. -/
lemma loop_deltaPlus (X : Finset Unit) :
    DeltaPlus (fun _ : Unit => ()) (fun _ : Unit => ()) X = ∅ := by
  unfold DeltaPlus; ext a; simp

lemma loop_deltaMinus (X : Finset Unit) :
    DeltaMinus (fun _ : Unit => ()) (fun _ : Unit => ()) X = ∅ := by
  unfold DeltaMinus; ext a; simp

theorem solution : ¬ (∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (ρ : Finset V → WithTop ℝ) (hρ : Submodular ρ) (hρEmpty : ρ ∅ = 0)
    (hρV : ρ (Finset.univ : Finset V) = 0),
    ((∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ) ↔
      (∀ X : Finset V,
        UpperCapOf cUpper (DeltaMinus tail head X) +
            NegLowerCapOf cLower (DeltaPlus tail head X) + ρ X ≥ 0)) ∧
    (IsIntegerUpper cUpper → IsIntegerLower cLower → IsIntegerUpper ρ →
      (∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ) →
      ∃ ξ : A → ℤ, FeasibleFlowMSFP1 tail head cUpper cLower ρ (fun a => (ξ a : ℝ)))) := by
  intro h
  have hsub : Submodular (fun _ : Finset Unit => (0 : WithTop ℝ)) := by
    intro X Y; simp
  have h1 := (@h Unit Unit _ _ _ (fun _ => ()) (fun _ => ()) (fun _ => ((0 : ℝ) : WithTop ℝ))
    (fun _ => ((1 : ℝ) : WithBot ℝ)) (fun _ => 0) hsub rfl rfl).1
  have hcond : ∀ X : Finset Unit,
      UpperCapOf (fun _ : Unit => ((0 : ℝ) : WithTop ℝ))
          (DeltaMinus (fun _ : Unit => ()) (fun _ : Unit => ()) X) +
        NegLowerCapOf (fun _ : Unit => ((1 : ℝ) : WithBot ℝ))
          (DeltaPlus (fun _ : Unit => ()) (fun _ : Unit => ()) X) +
        (fun _ : Finset Unit => (0 : WithTop ℝ)) X ≥ 0 := by
    intro X
    rw [loop_deltaPlus, loop_deltaMinus]
    simp [UpperCapOf, NegLowerCapOf]
  obtain ⟨ξ, hξ, -⟩ := h1.mpr hcond
  obtain ⟨hlo, hhi⟩ := hξ ()
  have a1 : (1 : ℝ) ≤ ξ () := WithBot.coe_le_coe.mp hlo
  have a2 : ξ () ≤ 0 := WithTop.coe_le_coe.mp hhi
  linarith

#print axioms solution
