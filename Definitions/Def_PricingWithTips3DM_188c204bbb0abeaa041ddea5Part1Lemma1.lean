import Definitions.Def_PricingWithTips3DM_8fb65f62dc7f7936c2bf07db
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem entry_length_le_entries_length
    {entry : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)} (hentry : entry ∈ entries) :
    (encodeIndexedOccurrenceEntry entry).length ≤
      (encodeIndexedOccurrenceEntries entries).length := by
  have hmem : (encodeIndexedOccurrenceEntry entry).length ∈
      entries.map (fun current =>
        (encodeIndexedOccurrenceEntry current).length) := by
    exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
  have hsum := List.le_sum_of_mem hmem
  simpa [encodeIndexedOccurrenceEntries, List.length_flatMap] using hsum
end CLRS.Chapter34.Turing.TMClique
