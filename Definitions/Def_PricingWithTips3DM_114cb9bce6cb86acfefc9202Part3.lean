import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

def compatibilityEdges_restoreVertexTicksRun
    (count : Nat) (input work₁ tail : List UnaryFrameSym)
    (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ buffer₂ test
        input output work₁ (List.replicate count .tick ++ tail) upper 0 0)
      (some (compatibilityEdgesCfg .taggedRestoreVertex buffer₁
        (if count = 0 then buffer₂ else some .tick) test input output
        (List.replicate count .tick ++ work₁) tail upper 0 0))
      (2 * count) := by
  induction count generalizing buffer₂ work₁ with
  | zero =>
      exact ⟨⟨0, by simp⟩, le_rfl⟩
  | succ count ih =>
      let afterPush := compatibilityEdgesCfg .taggedRestoreVertex buffer₁
        (some .tick) test input output (.tick :: work₁)
        (List.replicate count .tick ++ tail) upper 0 0
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ buffer₂ test
            input output work₁
            (List.replicate (count + 1) .tick ++ tail) upper 0 0)
          (some afterPush) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, afterPush,
            List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₂ := some .tick) (work₁ := .tick :: work₁)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * count) _ afterPush _ first rest
      convert full using 1 <;> try omega
      simp only [Nat.succ_ne_zero, if_false, ite_self,
        replicate_tick_append_tick]

/-- Exact budget for restoring one tagged occurrence row. -/
def compatibilityEdgesRestoreTaggedRowSteps
    (prior : IndexedOccurrence × Nat) : Nat :=
  2 * prior.2 + prior.1.clauseIndex +
    occurrencePolarityCode prior.1.literal +
    occurrenceVariableCode prior.1.literal + 7
end TMClique
end Turing
end Chapter34
end CLRS
