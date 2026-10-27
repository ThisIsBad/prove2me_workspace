import Definitions.Def_PricingWithTips3DM_8fb65f62dc7f7936c2bf07db
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem entries_length_le_encoding_length
    (entries : List (IndexedOccurrence × Nat)) :
    entries.length ≤ (encodeIndexedOccurrenceEntries entries).length := by
  rw [encodeIndexedOccurrenceEntries, List.length_flatMap]
  have hsum := List.length_le_sum_of_one_le
    (entries.map fun entry => (encodeIndexedOccurrenceEntry entry).length)
    (by
      intro length hlength
      rcases List.mem_map.mp hlength with ⟨entry, _, rfl⟩
      simp [encodeIndexedOccurrenceEntry])
  simpa using hsum
end CLRS.Chapter34.Turing.TMClique
