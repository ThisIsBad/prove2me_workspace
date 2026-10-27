import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem outer_iteration_symbols_length_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    (encodeReversedOccurrenceEntries priors.reverse).length ≤
      (encodeIndexedOccurrenceEntries (current :: priors)).length := by
  rw [encodeReversedOccurrenceEntries_length,
    encodeIndexedOccurrenceEntries_reverse_length]
  simp [encodeIndexedOccurrenceEntries]

end CLRS.Chapter34.Turing.TMClique
