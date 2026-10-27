import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem outer_iteration_restore_steps_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesRestoreTaggedRowsSteps priors.reverse ≤
      9 * (encodeIndexedOccurrenceEntries (current :: priors)).length *
          ((encodeIndexedOccurrenceEntries (current :: priors)).length + 1) + 1 := by
  let entries := current :: priors
  let bound := (encodeIndexedOccurrenceEntries entries).length
  have hrestoreEach : ∀ prior ∈ priors.reverse,
      compatibilityEdgesRestoreTaggedRowSteps prior + 1 ≤
        9 * (bound + 1) := by
    intro prior hprior
    have hprior' : prior ∈ priors := by simpa using hprior
    have hmem : prior ∈ entries := by simp [entries, hprior']
    have hrestore := restore_steps_le hmem
    change compatibilityEdgesRestoreTaggedRowSteps prior ≤
      8 * (bound + 1) at hrestore
    omega
  have hrestoreSum := sum_map_le_mul priors.reverse
    (fun prior => compatibilityEdgesRestoreTaggedRowSteps prior + 1)
    (9 * (bound + 1)) hrestoreEach
  have hentriesLength := entries_length_le_encoding_length entries
  have hpriorsLength : priors.length ≤ bound := by
    change entries.length ≤ bound at hentriesLength
    simp only [entries, List.length_cons] at hentriesLength
    omega
  have hreverseLength : priors.reverse.length ≤ bound := by
    simpa using hpriorsLength
  simp only [compatibilityEdgesRestoreTaggedRowsSteps]
  change _ ≤ 9 * bound * (bound + 1) + 1
  nlinarith

end CLRS.Chapter34.Turing.TMClique
