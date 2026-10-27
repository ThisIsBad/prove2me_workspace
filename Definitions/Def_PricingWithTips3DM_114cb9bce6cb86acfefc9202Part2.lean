import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

def compatibilityEdges_restoreFieldRun
    (field : CompatibilityRestoreField) (count : Nat)
    (input work₁ tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (compatibilityRestoreFieldLabel field)
        buffer₁ buffer₂ test input output work₁
        (List.replicate count .tick ++ .separator :: tail) upper 0 0)
      (some (compatibilityEdgesCfg (compatibilityRestoreFieldNext field)
        buffer₁ (some .separator) test input output
        (.separator :: List.replicate count .tick ++ work₁) tail
        upper 0 0)) (count + 1) := by
  induction count generalizing buffer₂ work₁ with
  | zero =>
      cases field <;>
        exact ⟨⟨1, by
          simp [flip, compatibilityRestoreFieldLabel,
            compatibilityRestoreFieldNext, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  | succ count ih =>
      let after := compatibilityEdgesCfg
        (compatibilityRestoreFieldLabel field) buffer₁ (some .tick) test
        input output (.tick :: work₁)
        (List.replicate count .tick ++ .separator :: tail) upper 0 0
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (compatibilityRestoreFieldLabel field)
            buffer₁ buffer₂ test input output work₁
            (List.replicate (count + 1) .tick ++ .separator :: tail)
            upper 0 0) (some after) 1 := by
        cases field <;>
          exact ⟨⟨1, by
            simp [flip, after, compatibilityRestoreFieldLabel,
              List.replicate_succ, step,
              compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
            le_rfl⟩
      have rest := ih (buffer₂ := some .tick) (work₁ := .tick :: work₁)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (count + 1) _ after _ first rest
      simpa only [separator_replicate_tick_append_tick, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full
end TMClique
end Turing
end Chapter34
end CLRS
