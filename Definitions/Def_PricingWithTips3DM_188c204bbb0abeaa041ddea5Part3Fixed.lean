import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Symbols
import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Fields
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem outer_iteration_fixed_steps_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    1 + (current.1.clauseIndex + occurrenceVariableCode current.1.literal + 2) +
        compatibilityEdgesFinishIterationSteps current.2
          (encodeReversedOccurrenceEntries priors.reverse) ≤
      4 * (encodeIndexedOccurrenceEntries (current :: priors)).length + 6 := by
  have hfields := outer_iteration_fields_steps_le current priors
  have hsymbols := outer_iteration_symbols_length_le current priors
  simp only [compatibilityEdgesFinishIterationSteps]
  omega

end CLRS.Chapter34.Turing.TMClique
