import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
namespace PricingWithTips.FixedShape3DM
open Hardness Hardness.Cert Hardness.Sat3dm

theorem baseCNF_clause_witness (input : List CLRS.Chapter34.CNFSym)
    (h : CLRS.Chapter34.isThreeCNFBool
      (CLRS.Chapter34.decodeCNF input) = true)
    {c : Hardness.Clause ℕ} (hc : c ∈ baseCNF input) :
    ∃ clause ∈ CLRS.Chapter34.decodeCNF input,
      c = (clause.map CLRS3CNFBridge.certLiteral).map
        Hardness.Cert.litOf := by
  unfold baseCNF at hc
  simp only [CLRS3CNFBridge.guardedCertCNF, h, if_true,
    Hardness.Cert.decodeCNF, CLRS3CNFBridge.certCNF,
    List.mem_map] at hc
  obtain ⟨encoded, hencoded, rfl⟩ := hc
  obtain ⟨clause, hclause, rfl⟩ := hencoded
  exact ⟨clause, hclause, rfl⟩

end PricingWithTips.FixedShape3DM
