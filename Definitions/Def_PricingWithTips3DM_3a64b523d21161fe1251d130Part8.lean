import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part7
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

theorem reduction_correct (input : List CLRS.Chapter34.CNFSym) :
    input ∈ CLRS.Chapter34.ThreeCNFSat ↔ ThreeDMYes (reduction input) := by
  calc
    input ∈ CLRS.Chapter34.ThreeCNFSat ↔ (paddedCNF input).Satisfiable :=
      threeCNFSat_iff_paddedCNF input
    _ ↔ MATCHING_3D (abstractInstance input) := by
      exact satisfiable_iff_matching input
    _ ↔ MATCHING_3D (normalizedInstance input) := matching_normalized_iff input
    _ ↔ HasPerfectFinset3DM (dimension input) (normalizedTriples input) := Iff.rfl
    _ ↔ HasPerfect3DMatching (dimension input)
        (fun b s d => decide ((b, s, d) ∈ normalizedTriples input)) :=
      PricingWithTips.finset3DM_iff_allocation3DM _ _
    _ ↔ ThreeDMYes (reduction input) := Iff.rfl
end PricingWithTips.FixedShape3DM
