import Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1StepZero
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

def compatibilityEdges_copyCounterTickRun
    (counter : CompatibilityEdgeCounter) (remaining saved other : Nat)
    (input work₁ work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgeCounterCfg counter (compatibilityEdgeCopyLabel counter)
        buffer₁ buffer₂ test input output work₁ work₂
        (remaining + 1) other saved)
      (some (compatibilityEdgeCounterCfg counter
        (compatibilityEdgeCopyLabel counter) buffer₁ buffer₂ true input
        (.tick :: output) work₁ work₂ remaining other (saved + 1))) 3 := by
  cases counter <;> exact ⟨⟨3, by
    simp [Function.iterate_succ_apply, flip, compatibilityEdgeCounterCfg,
      compatibilityEdgeCopyLabel, List.replicate_succ, step,
      compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
end TMClique
end Turing
end Chapter34
end CLRS
