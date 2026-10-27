import Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1Basic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

def compatibilityEdges_copyCounterZeroRun
    (counter : CompatibilityEdgeCounter) (saved other : Nat)
    (input work₁ work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgeCounterCfg counter (compatibilityEdgeCopyLabel counter)
        buffer₁ buffer₂ test input output work₁ work₂ 0 other saved)
      (some (compatibilityEdgeCounterCfg counter
        (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ false
        input output work₁ work₂ 0 other saved)) 1 := by
  cases counter <;> exact ⟨⟨1, by
    simp [flip, compatibilityEdgeCounterCfg, compatibilityEdgeCopyLabel,
      compatibilityEdgeRestoreLabel, step, compatibilityEdgesProgram,
      compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
end TMClique
end Turing
end Chapter34
end CLRS
