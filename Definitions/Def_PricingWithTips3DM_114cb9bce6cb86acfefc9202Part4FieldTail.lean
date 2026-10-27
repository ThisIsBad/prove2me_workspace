import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4FieldHead
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

def compatibilityEdges_restoreTaggedRowFieldTailRun
    (priorClause priorVertex : Nat) (priorLiteral : Literal)
    (rowFlag : UnaryFrameSym) (input work₁ tail : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ : Option UnaryFrameSym)
    (test : Bool) (upper : Nat) :
    Σ finalBuffer₂ : Option UnaryFrameSym,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .taggedRestoreClause buffer₁ (some .separator)
          test input output
          (.separator :: List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++
            .separator :: List.replicate (occurrenceVariableCode priorLiteral) .tick ++
              .separator :: .frameEnd :: rowFlag :: work₁)
          (List.replicate priorClause .tick ++ .separator ::
            List.replicate priorVertex .tick ++ tail) upper 0 0)
        (some (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ finalBuffer₂
          test input output
          (List.replicate priorVertex .tick ++ .separator ::
            List.replicate priorClause .tick ++ .separator ::
              List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
                List.replicate (occurrenceVariableCode priorLiteral) .tick ++
                  .separator :: .frameEnd :: rowFlag :: work₁)
          tail upper 0 0)) (2 * priorVertex + (priorClause + 1)) := by
  have clauseRun := compatibilityEdges_restoreFieldRun .clause priorClause input
    (.separator :: List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++
      .separator :: List.replicate (occurrenceVariableCode priorLiteral) .tick ++
        .separator :: .frameEnd :: rowFlag :: work₁)
    (List.replicate priorVertex .tick ++ tail)
    output buffer₁ (some .separator) test upper
  have vertexRun := compatibilityEdges_restoreVertexTicksRun priorVertex input
    (.separator :: List.replicate priorClause .tick ++ .separator ::
      List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
        List.replicate (occurrenceVariableCode priorLiteral) .tick ++
          .separator :: .frameEnd :: rowFlag :: work₁)
    tail output buffer₁ (some .separator) test upper
  refine ⟨if priorVertex = 0 then some .separator else some .tick, ?_⟩
  exact EvalsToInTime.trans (step compatibilityEdgesProgram) _ _ _ _ _
    (by simpa [compatibilityRestoreFieldLabel, compatibilityRestoreFieldNext,
      List.append_assoc] using clauseRun)
    (by simpa [List.append_assoc] using vertexRun)

end TMClique
end Turing
end Chapter34
end CLRS
