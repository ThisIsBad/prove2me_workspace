import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

def dimension (input : List CLRS.Chapter34.CNFSym) : ℕ :=
  (input.length + 1) * (input.length * 2)

def triples (input : List CLRS.Chapter34.CNFSym) :=
  Sat3dm.tripleSet (paddedCNF input) (variableList input)

theorem dimension_eq_ext_card (input : List CLRS.Chapter34.CNFSym) :
    dimension input = (variableList input).length.succ * ((paddedCNF input).length * 2) := by
  simp [dimension, variableList, paddedCNF_length]

theorem satisfiable_iff_matching (input : List CLRS.Chapter34.CNFSym) :
    (paddedCNF input).Satisfiable ↔
      ∃ M ⊆ triples input, IsExactCover M (fun t ↦ t.1) ∧
        IsExactCover M (fun t ↦ t.2.1) ∧ IsExactCover M (fun t ↦ t.2.2) := by
  simpa [triples, variableList, paddedCNF_length] using
    Sat3dm.satisfiable_iff_exists_matching
      (paddedCNF input) (variableList input) (variable_coverage input)

theorem ext_card_eq_dimension (input : List CLRS.Chapter34.CNFSym) :
    ((variableList input).length + 1) * ((paddedCNF input).length * 2) =
      dimension input := by
  simp [variableList, paddedCNF_length, dimension]

theorem slot_card_eq_dimension (input : List CLRS.Chapter34.CNFSym) :
    ((variableList input).length + 1) * (paddedCNF input).length +
        ((paddedCNF input).length +
          (paddedCNF input).length * (variableList input).length) =
      dimension input := by
  simp only [variableList, List.length_range, paddedCNF_length, dimension]
  ring
end PricingWithTips.FixedShape3DM
