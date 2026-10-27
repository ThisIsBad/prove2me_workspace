import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3Base
import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3Padding
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem variable_coverage (input : List CLRS.Chapter34.CNFSym) :
    ∀ c ∈ paddedCNF input, ∀ l ∈ c, l.var ∈ variableList input := by
  intro c hc l hl
  rw [paddedCNF, List.mem_append] at hc
  rcases hc with hc | hc
  · exact baseCNF_variable_coverage input hc hl
  · exact padding_variable_coverage input hc hl

end PricingWithTips.FixedShape3DM
