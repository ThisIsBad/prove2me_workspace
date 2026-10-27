import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Clause
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem entry_variable_le_entry_length (entry : IndexedOccurrence × Nat) :
    occurrenceVariableCode entry.1.literal ≤
      (encodeIndexedOccurrenceEntry entry).length := by
  have h := value_le_encodeUnaryFrame_length
    (value := occurrenceVariableCode entry.1.literal)
    (values := indexedOccurrenceRowValues entry.2 entry.1)
    (by simp [indexedOccurrenceRowValues])
  simpa [encodeIndexedOccurrenceEntry] using
    h.trans (Nat.le_add_right (encodeUnaryFrame
      (indexedOccurrenceRowValues entry.2 entry.1)).length 1)

end CLRS.Chapter34.Turing.TMClique
