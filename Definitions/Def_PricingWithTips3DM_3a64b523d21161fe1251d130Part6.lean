import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part5
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

def normalizedTriples (input : List CLRS.Chapter34.CNFSym) :
    Finset (ThreeDMTriple (dimension input)) :=
  (triples input).image
    (fun t => (wMap input t.1,
      (slotMap input t.2.1, slotMap input t.2.2)))

def reduction (input : List CLRS.Chapter34.CNFSym) : ThreeDMInstance :=
  ⟨dimension input,
    fun b s d => decide ((b, s, d) ∈ normalizedTriples input)⟩

def abstractInstance (input : List CLRS.Chapter34.CNFSym) : Matching3DInstance where
  W := Sat3dm.Ext (variableList input).length (paddedCNF input).length
  X := Sat3dm.Slot (variableList input).length (paddedCNF input).length
  Y := Sat3dm.Slot (variableList input).length (paddedCNF input).length
  triples := triples input

def normalizedInstance (input : List CLRS.Chapter34.CNFSym) : Matching3DInstance where
  W := Fin (dimension input)
  X := Fin (dimension input)
  Y := Fin (dimension input)
  triples := normalizedTriples input
end PricingWithTips.FixedShape3DM
