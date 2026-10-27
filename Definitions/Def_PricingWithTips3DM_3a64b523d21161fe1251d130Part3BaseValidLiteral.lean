import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValidBound
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem converted_clause_variable_coverage
    (input : List CLRS.Chapter34.CNFSym)
    {clause : CLRS.Chapter34.Clause}
    (hclause : clause ∈ CLRS.Chapter34.decodeCNF input)
    {l : Hardness.Literal ℕ}
    (hl : l ∈ (clause.map CLRS3CNFBridge.certLiteral).map
      Hardness.Cert.litOf) :
    l.var ∈ variableList input := by
  simp only [List.mem_map] at hl
  obtain ⟨encoded, hencoded, rfl⟩ := hl
  obtain ⟨literal, hliteral, rfl⟩ := hencoded
  simpa [variableList] using
    certified_literal_variable_lt input hclause hliteral

end PricingWithTips.FixedShape3DM
