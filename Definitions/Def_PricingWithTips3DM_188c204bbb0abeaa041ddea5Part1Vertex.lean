import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Lemma1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem entry_vertex_le_entry_length (entry : IndexedOccurrence × Nat) :
    entry.2 ≤ (encodeIndexedOccurrenceEntry entry).length := by
  rcases entry with ⟨⟨clause, position, literal⟩, vertex⟩
  cases literal <;>
    simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
      encodeUnaryFrame_length, occurrencePolarityCode,
      occurrenceVariableCode] <;> omega

end CLRS.Chapter34.Turing.TMClique
