import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem certified_literal_variable_lt (input : List CLRS.Chapter34.CNFSym)
    {clause : CLRS.Chapter34.Clause}
    (hclause : clause ∈ CLRS.Chapter34.decodeCNF input)
    {literal : CLRS.Chapter34.Literal} (hliteral : literal ∈ clause) :
    (Hardness.Cert.litOf
      (CLRS3CNFBridge.certLiteral literal)).var < input.length := by
  have hbound := CLRS.Chapter34.decodeCNF_indices_lt
    input clause hclause literal hliteral
  cases literal <;> simpa [Hardness.Cert.litOf,
    CLRS3CNFBridge.certLiteral, CLRS.Chapter34.litIndex] using hbound

end PricingWithTips.FixedShape3DM
