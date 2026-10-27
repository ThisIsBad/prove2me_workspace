import Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1Extend
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

def compatibilityEdges_copyCounterRun
    (counter : CompatibilityEdgeCounter) (remaining saved : Nat)
    (input work₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (other : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgeCounterCfg counter (compatibilityEdgeCopyLabel counter)
        buffer₁ buffer₂ test input output work₁ work₂
        remaining other saved)
      (some (compatibilityEdgeCounterCfg counter
        (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ false
        input (List.replicate remaining .tick ++ output) work₁ work₂
        0 other (saved + remaining))) (3 * remaining + 1) := by
  induction remaining generalizing saved test output with
  | zero =>
      simpa using compatibilityEdges_copyCounterZeroRun counter saved other
        input work₁ work₂ output buffer₁ buffer₂ test
  | succ remaining ih =>
      have rest := ih (saved := saved + 1) (test := true)
        (output := .tick :: output)
      exact compatibilityEdges_copyCounterExtendRun counter remaining saved other
        input work₁ work₂ output buffer₁ buffer₂ test rest
end TMClique
end Turing
end Chapter34
end CLRS
