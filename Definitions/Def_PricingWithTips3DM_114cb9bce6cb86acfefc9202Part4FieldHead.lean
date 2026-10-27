import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Prefix
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

def compatibilityEdges_restoreTaggedRowFieldHeadRun
    (priorClause priorVertex : Nat) (priorLiteral : Literal)
    (rowFlag : UnaryFrameSym) (input work₁ tail : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ : Option UnaryFrameSym)
    (test : Bool) (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .taggedRestoreVariable buffer₁ (some .separator)
        test input output (.separator :: .frameEnd :: rowFlag :: work₁)
        (List.replicate (occurrenceVariableCode priorLiteral) .tick ++ .separator ::
          List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
            List.replicate priorClause .tick ++ .separator ::
              List.replicate priorVertex .tick ++ tail) upper 0 0)
      (some (compatibilityEdgesCfg .taggedRestoreClause buffer₁ (some .separator)
        test input output
        (.separator :: List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++
          .separator :: List.replicate (occurrenceVariableCode priorLiteral) .tick ++
            .separator :: .frameEnd :: rowFlag :: work₁)
        (List.replicate priorClause .tick ++ .separator ::
          List.replicate priorVertex .tick ++ tail) upper 0 0))
      (((occurrencePolarityFlag priorLiteral).toNat + 1) +
        (occurrenceVariableCode priorLiteral + 1)) := by
  have variableRun := compatibilityEdges_restoreFieldRun .variable
    (occurrenceVariableCode priorLiteral) input
    (.separator :: .frameEnd :: rowFlag :: work₁)
    (List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
      List.replicate priorClause .tick ++ .separator :: List.replicate priorVertex .tick ++ tail)
    output buffer₁ (some .separator) test upper
  have polarityRun := compatibilityEdges_restoreFieldRun .polarity
    (occurrencePolarityFlag priorLiteral).toNat input
    (.separator :: List.replicate (occurrenceVariableCode priorLiteral) .tick ++
      .separator :: .frameEnd :: rowFlag :: work₁)
    (List.replicate priorClause .tick ++ .separator :: List.replicate priorVertex .tick ++ tail)
    output buffer₁ (some .separator) test upper
  exact EvalsToInTime.trans (step compatibilityEdgesProgram) _ _ _ _ _
    (by simpa [compatibilityRestoreFieldLabel, compatibilityRestoreFieldNext,
      List.append_assoc] using variableRun)
    (by simpa [compatibilityRestoreFieldLabel, compatibilityRestoreFieldNext,
      List.append_assoc] using polarityRun)

end TMClique
end Turing
end Chapter34
end CLRS
