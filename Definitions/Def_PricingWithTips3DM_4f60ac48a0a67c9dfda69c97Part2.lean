import Definitions.Def_PricingWithTips3DM_4f60ac48a0a67c9dfda69c97Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

def compatibilityEdges_clearVariableRun
    (variableCode : Nat)
    (input outputWork₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .clearCurrentVariable buffer₁ buffer₂ test
        input output outputWork₁ work₂ upper 0 variableCode)
      (some (compatibilityEdgesCfg .taggedRestoreStart buffer₁ buffer₂
        false input output outputWork₁ work₂ upper 0 0))
      (variableCode + 1) := by
  induction variableCode generalizing test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp]⟩, le_rfl⟩
  | succ variableCode ih =>
      let after := compatibilityEdgesCfg .clearCurrentVariable buffer₁ buffer₂
        true input output outputWork₁ work₂ upper 0 variableCode
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .clearCurrentVariable buffer₁ buffer₂ test
            input output outputWork₁ work₂ upper 0
            (variableCode + 1)) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp, List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (variableCode + 1) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm] using full
end TMClique
end Turing
end Chapter34
end CLRS
