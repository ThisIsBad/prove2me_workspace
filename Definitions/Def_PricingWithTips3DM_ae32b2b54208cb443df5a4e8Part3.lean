import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

theorem encodeCompatibleOccurrencePairIterations
    (entries : List (IndexedOccurrence × Nat)) :
    TMClique.encodeCompatibleOccurrenceIterations entries =
      (compatibleOccurrencePairIterations entries).flatMap
        encodeCliqueEdge := by
  induction entries with
  | nil => rfl
  | cons current priors ih =>
      simp only [TMClique.encodeCompatibleOccurrenceIterations,
        compatibleOccurrencePairIterations, List.flatMap_append]
      rw [ih, encodeCompatibleOccurrencePairs]

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
