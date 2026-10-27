import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem outer_iteration_scan_steps_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesCurrentRowSteps current +
        compatibilityEdgesPriorRowsSteps current priors ≤
      30 * (encodeIndexedOccurrenceEntries (current :: priors)).length *
          ((encodeIndexedOccurrenceEntries (current :: priors)).length + 1) +
        10 * ((encodeIndexedOccurrenceEntries (current :: priors)).length + 1) := by
  let entries := current :: priors
  let bound := (encodeIndexedOccurrenceEntries entries).length
  have hcurrent : current ∈ entries := by simp [entries]
  have hcurrentSteps := current_steps_le hcurrent
  have hpriorEach : ∀ prior ∈ priors,
      compatibilityEdgesPriorRowSteps current prior ≤ 30 * (bound + 1) := by
    intro prior hprior
    have hmem : prior ∈ entries := by simp [entries, hprior]
    simpa [bound] using prior_steps_le hcurrent hmem
  have hpriorSum := sum_map_le_mul priors
    (compatibilityEdgesPriorRowSteps current) (30 * (bound + 1)) hpriorEach
  have hentriesLength := entries_length_le_encoding_length entries
  have hpriorsLength : priors.length ≤ bound := by
    change entries.length ≤ bound at hentriesLength
    simp only [entries, List.length_cons] at hentriesLength
    omega
  simp only [compatibilityEdgesPriorRowsSteps]
  change _ ≤ 30 * bound * (bound + 1) + 10 * (bound + 1)
  nlinarith

end CLRS.Chapter34.Turing.TMClique
