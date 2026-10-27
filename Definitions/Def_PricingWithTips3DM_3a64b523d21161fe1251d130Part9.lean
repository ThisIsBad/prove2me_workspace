import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part8
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

theorem threeDM_np_hard_of_reduction_polytime
    (hreduction : Nonempty (Turing.TM2ComputableInPolyTime
      (id : List CLRS.Chapter34.CNFSym → List CLRS.Chapter34.CNFSym)
      encodeThreeDMInstance reduction)) :
    NPHardMarketPredicate ThreeDMYes := by
  intro Γ L hL
  obtain ⟨f, hf, hcorrect⟩ :=
    CLRS3DM.clrs_threeCNFSat_npHard Γ L
      (CLRS3DM.polynomiallyVerifiable_to_CLRS hL)
  refine ⟨reduction ∘ f, ?_, ?_⟩
  · exact CLRS.Chapter34.PolyTimeComputable.comp hf hreduction
  · intro x
    exact (hcorrect x).trans (reduction_correct (f x))
end PricingWithTips.FixedShape3DM
