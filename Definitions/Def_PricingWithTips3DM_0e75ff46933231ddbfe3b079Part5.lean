import Definitions.Def_PricingWithTips3DM_0e75ff46933231ddbfe3b079Part4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Once no prior row remains, the next controller step enters current-counter
cleanup and clears the stale work-one buffer. -/
def compatibilityEdges_priorRowsDoneRun
    (current : IndexedOccurrence × Nat)
    (work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg
        (.priorStart (occurrencePolarityFlag current.1.literal))
        buffer₁ buffer₂ test [] output [] work₂ current.2
        current.1.clauseIndex (occurrenceVariableCode current.1.literal))
      (some (compatibilityEdgesCfg .clearCurrentClause none buffer₂ test []
        output [] work₂ current.2 current.1.clauseIndex
        (occurrenceVariableCode current.1.literal))) 1 := by
  exact ⟨⟨1, by rfl⟩, le_rfl⟩
end TMClique
end Turing
end Chapter34
end CLRS
