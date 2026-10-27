import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValid
import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseInvalid
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem baseCNF_variable_coverage (input : List CLRS.Chapter34.CNFSym)
    {c : Hardness.Clause ℕ} (hc : c ∈ baseCNF input)
    {l : Hardness.Literal ℕ} (hl : l ∈ c) :
    l.var ∈ variableList input := by
  by_cases h : CLRS.Chapter34.isThreeCNFBool
      (CLRS.Chapter34.decodeCNF input) = true
  · exact baseCNF_variable_coverage_valid input h hc hl
  · exact baseCNF_variable_coverage_invalid input h hc hl

end PricingWithTips.FixedShape3DM
