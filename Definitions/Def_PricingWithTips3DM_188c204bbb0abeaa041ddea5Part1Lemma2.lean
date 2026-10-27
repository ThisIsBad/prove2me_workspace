import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Variable
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem entry_fields_le_entries_length
    {entry : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)} (hentry : entry ∈ entries) :
    entry.2 ≤ (encodeIndexedOccurrenceEntries entries).length ∧
    entry.1.clauseIndex ≤ (encodeIndexedOccurrenceEntries entries).length ∧
    occurrenceVariableCode entry.1.literal ≤
      (encodeIndexedOccurrenceEntries entries).length := by
  have hlength := entry_length_le_entries_length hentry
  exact ⟨(entry_vertex_le_entry_length entry).trans hlength,
    (entry_clause_le_entry_length entry).trans hlength,
    (entry_variable_le_entry_length entry).trans hlength⟩
end CLRS.Chapter34.Turing.TMClique
