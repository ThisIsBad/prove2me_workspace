import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

theorem encodeCompatibleOccurrencePair
    (current prior : IndexedOccurrence × Nat) :
    TMClique.encodeCompatibleOccurrenceEdge current prior =
      (compatibleOccurrencePair current prior).flatMap encodeCliqueEdge := by
  cases hcompatible :
      TMClique.indexedOccurrencesCompatibleCode current prior <;>
    simp [TMClique.encodeCompatibleOccurrenceEdge,
      compatibleOccurrencePair, hcompatible]

theorem encodeCompatibleOccurrencePairs
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    TMClique.encodeCompatibleOccurrenceEdges current priors =
      (compatibleOccurrencePairs current priors).flatMap encodeCliqueEdge := by
  unfold TMClique.encodeCompatibleOccurrenceEdges compatibleOccurrencePairs
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro prior _
  exact encodeCompatibleOccurrencePair current prior

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
