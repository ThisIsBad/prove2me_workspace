import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Normalize
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

/-- Exact local run from a previously consumed tag marker through one reversed
row.  The row is restored in forward order above work one, followed by its
one-symbol compatibility flag. -/
def compatibilityEdges_restoreTaggedRowRun
    (prior : IndexedOccurrence × Nat) (compatible : Bool)
    (input work₁ tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) (upper : Nat) :
    Σ finalBuffer₂ : Option UnaryFrameSym,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .taggedRestoreFlag buffer₁ buffer₂ test
          input output work₁
          ((if compatible then .tick else .frameEnd) ::
            (encodeIndexedOccurrenceEntry prior).reverse ++ tail) upper 0 0)
        (some (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ finalBuffer₂
          test input output
          (encodeIndexedOccurrenceEntry prior ++
            [if compatible then .tick else .separator] ++ work₁)
          tail upper 0 0))
        (compatibilityEdgesRestoreTaggedRowSteps prior) := by
  rcases prior with ⟨priorOccurrence, priorVertex⟩
  rcases priorOccurrence with ⟨priorClause, priorPosition, priorLiteral⟩
  rcases compatibilityEdges_restoreTaggedRowComposedRun priorClause priorPosition
    priorVertex priorLiteral compatible input work₁ tail output buffer₁ buffer₂
    test upper with ⟨finalBuffer₂, run⟩
  refine ⟨finalBuffer₂, ?_⟩
  rw [compatibilityEdges_restoreTaggedRow_work_eq priorClause priorPosition
    priorVertex priorLiteral compatible work₁] at run
  rw [compatibilityEdges_restoreTaggedRow_steps_eq priorClause priorPosition
    priorVertex priorLiteral] at run
  exact run

end TMClique
end Turing
end Chapter34
end CLRS
