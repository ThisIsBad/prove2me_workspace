import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

theorem tautClause_sat (σ : ℕ → Bool) :
    Hardness.Clause.Sat σ tautClause := by
  cases h : σ 0 <;> simp [tautClause, Hardness.Clause.Sat,
    Hardness.Literal.Holds, h]

theorem paddedCNF_satisfiable_iff (input : List CLRS.Chapter34.CNFSym) :
    (paddedCNF input).Satisfiable ↔ (baseCNF input).Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun c hc => hσ c (List.mem_append_left _ hc)⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro c hc
    rw [paddedCNF, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hσ c hc
    · have : c = tautClause := by
        simpa using (List.eq_of_mem_replicate hc)
      simpa [this] using tautClause_sat σ

theorem threeCNFSat_iff_paddedCNF (input : List CLRS.Chapter34.CNFSym) :
    input ∈ CLRS.Chapter34.ThreeCNFSat ↔ (paddedCNF input).Satisfiable := by
  rw [paddedCNF_satisfiable_iff]
  exact CLRS3CNFBridge.threeCNFSat_iff_guardedCertSAT input
end PricingWithTips.FixedShape3DM
