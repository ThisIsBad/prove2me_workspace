import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Compose
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

theorem compatibilityEdges_restoreTaggedRow_work_eq
    (priorClause priorPosition priorVertex : Nat) (priorLiteral : Literal)
    (compatible : Bool) (work₁ : List UnaryFrameSym) :
    List.replicate priorVertex .tick ++ .separator ::
      List.replicate priorClause .tick ++ .separator ::
        List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
          List.replicate (occurrenceVariableCode priorLiteral) .tick ++
            .separator :: .frameEnd ::
              (if compatible then .tick else .separator) :: work₁ =
      encodeIndexedOccurrenceEntry
          (⟨⟨priorClause, priorPosition, priorLiteral⟩, priorVertex⟩) ++
        [if compatible then .tick else .separator] ++ work₁ := by
  simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
    encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]

theorem compatibilityEdges_restoreTaggedRow_steps_eq
    (priorClause priorPosition priorVertex : Nat) (priorLiteral : Literal) :
    ((occurrenceVariableCode priorLiteral + 1) +
      ((occurrencePolarityFlag priorLiteral).toNat + 1) +
      (priorClause + 1) + 2 * priorVertex) + 4 =
      compatibilityEdgesRestoreTaggedRowSteps
        (⟨⟨priorClause, priorPosition, priorLiteral⟩, priorVertex⟩) := by
  simp [compatibilityEdgesRestoreTaggedRowSteps, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]
  omega

end TMClique
end Turing
end Chapter34
end CLRS
