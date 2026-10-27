import Mathlib
import Definitions.Def_IntractableCoding_Weights_NPComplete
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
import Theorems.Thm_PricingWithTips_threeDM_np_hard

open PricingWithTips IntractableCoding.Weights

theorem solution {α : Type} (enc : α → List Bool) (P : α → Prop)
    (g : ThreeDMInstance → α)
    (hg : Nonempty (Turing.TM2ComputableInPolyTime encodeThreeDMInstance enc g))
    (hred : ∀ I : ThreeDMInstance, ThreeDMYes I ↔ P (g I)) :
    NPHardFor enc P := by
  intro Γ L hL
  obtain ⟨f, ⟨hf⟩, hiff⟩ := threeDM_np_hard Γ L hL
  obtain ⟨hg'⟩ := hg
  refine ⟨g ∘ f, Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch hf hg', fun x => ?_⟩
  exact (hiff x).trans (hred (f x))
