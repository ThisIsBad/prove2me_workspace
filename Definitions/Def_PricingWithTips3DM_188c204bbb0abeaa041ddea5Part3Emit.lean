import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem outer_iteration_emit_steps_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesEmitPriorRowsSteps current priors ≤
      20 * (encodeIndexedOccurrenceEntries (current :: priors)).length *
        ((encodeIndexedOccurrenceEntries (current :: priors)).length + 1) := by
  let entries := current :: priors
  let bound := (encodeIndexedOccurrenceEntries entries).length
  have hcurrent : current ∈ entries := by simp [entries]
  have hemitEach : ∀ prior ∈ priors,
      compatibilityEdgesEmitPriorRowSteps current prior ≤
        20 * (bound + 1) := by
    intro prior hprior
    have hmem : prior ∈ entries := by simp [entries, hprior]
    simpa [bound] using emit_prior_steps_le hcurrent hmem
  have hemitSum := sum_map_le_mul priors
    (compatibilityEdgesEmitPriorRowSteps current) (20 * (bound + 1))
    hemitEach
  have hentriesLength := entries_length_le_encoding_length entries
  have hpriorsLength : priors.length ≤ bound := by
    change entries.length ≤ bound at hentriesLength
    simp only [entries, List.length_cons] at hentriesLength
    omega
  simp only [compatibilityEdgesEmitPriorRowsSteps]
  change _ ≤ 20 * bound * (bound + 1)
  nlinarith

end CLRS.Chapter34.Turing.TMClique
