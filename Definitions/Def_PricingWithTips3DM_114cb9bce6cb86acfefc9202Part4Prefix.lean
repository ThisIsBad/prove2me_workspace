import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

def compatibilityEdges_restoreTaggedRowPrefixRun
    (priorClause priorPosition priorVertex : Nat) (priorLiteral : Literal)
    (compatible : Bool) (input work₁ tail : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .taggedRestoreFlag buffer₁ buffer₂ test input output
        work₁ ((if compatible then .tick else .frameEnd) ::
          (encodeIndexedOccurrenceEntry
            (⟨⟨priorClause, priorPosition, priorLiteral⟩, priorVertex⟩)).reverse ++ tail)
        upper 0 0)
      (some (compatibilityEdgesCfg .taggedRestoreVariable buffer₁
        (some .separator) test input output
        (.separator :: .frameEnd ::
          (if compatible then .tick else .separator) :: work₁)
        (List.replicate (occurrenceVariableCode priorLiteral) .tick ++
          .separator :: List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++
            .separator :: List.replicate priorClause .tick ++
              .separator :: List.replicate priorVertex .tick ++ tail) upper 0 0)) 4 := by
  let rowFlag : UnaryFrameSym := if compatible then .tick else .separator
  let afterFlagBuffer₂ : Option UnaryFrameSym :=
    if compatible then some .tick else some .frameEnd
  let afterFlagWork₁ := rowFlag :: work₁
  have flagRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .taggedRestoreFlag buffer₁ buffer₂ test input output work₁
        ((if compatible then .tick else .frameEnd) ::
          (encodeIndexedOccurrenceEntry
            (⟨⟨priorClause, priorPosition, priorLiteral⟩, priorVertex⟩)).reverse ++ tail)
        upper 0 0)
      (some (compatibilityEdgesCfg .taggedRestoreFrameEnd buffer₁ afterFlagBuffer₂
        test input output afterFlagWork₁
        ((encodeIndexedOccurrenceEntry
          (⟨⟨priorClause, priorPosition, priorLiteral⟩, priorVertex⟩)).reverse ++ tail)
        upper 0 0)) 2 := by
    cases compatible <;> exact ⟨⟨2, by
      simp [Function.iterate_succ_apply, flip, rowFlag, afterFlagBuffer₂,
        afterFlagWork₁, step, compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
      le_rfl⟩
  let reversedFields :=
    (encodeUnaryFrame (indexedOccurrenceRowValues priorVertex
      ⟨priorClause, priorPosition, priorLiteral⟩)).reverse
  let afterEndWork₁ := .frameEnd :: afterFlagWork₁
  have endRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .taggedRestoreFrameEnd buffer₁ afterFlagBuffer₂ test
        input output afterFlagWork₁ (.frameEnd :: reversedFields ++ tail) upper 0 0)
      (some (compatibilityEdgesCfg .taggedRestoreVariableSeparator buffer₁
        (some .frameEnd) test input output afterEndWork₁
        (reversedFields ++ tail) upper 0 0)) 1 := by
    exact ⟨⟨1, by simp [flip, afterEndWork₁, step, compatibilityEdgesProgram,
      compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  let afterVariableSeparatorWork₁ := .separator :: afterEndWork₁
  let afterVariableSeparator :=
    List.replicate (occurrenceVariableCode priorLiteral) .tick ++ .separator ::
      List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
        List.replicate priorClause .tick ++ .separator ::
          List.replicate priorVertex .tick ++ tail
  have variableSeparatorRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .taggedRestoreVariableSeparator buffer₁ (some .frameEnd)
        test input output afterEndWork₁ (.separator :: afterVariableSeparator) upper 0 0)
      (some (compatibilityEdgesCfg .taggedRestoreVariable buffer₁ (some .separator)
        test input output afterVariableSeparatorWork₁ afterVariableSeparator upper 0 0)) 1 := by
    exact ⟨⟨1, by simp [flip, afterVariableSeparatorWork₁, step,
      compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram) 2 1 _ _ _ flagRun
    (by simpa [reversedFields, encodeIndexedOccurrenceEntry,
      List.reverse_append] using endRun)
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram) _ 1 _ _ _ first
    (by simpa [reversedFields, indexedOccurrenceRowValues, encodeUnaryFrame,
      encodeUnaryFrameBlock, afterVariableSeparator, List.reverse_append,
      List.append_assoc] using variableSeparatorRun)
  simpa [rowFlag, afterFlagWork₁, afterEndWork₁,
    afterVariableSeparatorWork₁, Nat.add_assoc] using second

end TMClique
end Turing
end Chapter34
end CLRS
