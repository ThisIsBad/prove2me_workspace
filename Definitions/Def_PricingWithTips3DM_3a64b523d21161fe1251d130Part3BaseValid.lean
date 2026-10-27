import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValidClause
import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3BaseValidLiteral
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem baseCNF_variable_coverage_valid (input : List CLRS.Chapter34.CNFSym)
    (h : CLRS.Chapter34.isThreeCNFBool
      (CLRS.Chapter34.decodeCNF input) = true)
    {c : Hardness.Clause ℕ} (hc : c ∈ baseCNF input)
    {l : Hardness.Literal ℕ} (hl : l ∈ c) :
    l.var ∈ variableList input := by
  obtain ⟨clause, hclause, rfl⟩ := baseCNF_clause_witness input h hc
  exact converted_clause_variable_coverage input hclause hl

end PricingWithTips.FixedShape3DM
