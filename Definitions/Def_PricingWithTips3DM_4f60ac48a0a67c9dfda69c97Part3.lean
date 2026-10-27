import Definitions.Def_PricingWithTips3DM_4f60ac48a0a67c9dfda69c97Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Exact cleanup run from populated current-row counters to the tagged-row
restoration entry.  The upper endpoint remains available in counter one. -/
def compatibilityEdges_cleanupCurrentRun
    (upper clause variableCode : Nat)
    (input outputWork₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .clearCurrentClause buffer₁ buffer₂ test
        input output outputWork₁ work₂ upper clause variableCode)
      (some (compatibilityEdgesCfg .taggedRestoreStart buffer₁ buffer₂
        false input output outputWork₁ work₂ upper 0 0))
      (clause + variableCode + 2) := by
  have first := compatibilityEdges_clearClauseRun clause input outputWork₁
    work₂ output buffer₁ buffer₂ test upper variableCode
  have rest := compatibilityEdges_clearVariableRun variableCode input
    outputWork₁ work₂ output buffer₁ buffer₂ false upper
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (clause + 1) (variableCode + 1) _ _ _ first rest
  convert full using 1 <;> omega
end TMClique
end Turing
end Chapter34
end CLRS
