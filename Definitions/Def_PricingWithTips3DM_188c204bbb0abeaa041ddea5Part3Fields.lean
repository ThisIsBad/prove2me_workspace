import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part2
import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Arithmetic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem outer_iteration_fields_steps_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    1 + (current.1.clauseIndex + occurrenceVariableCode current.1.literal + 2) +
        current.2 + 3 ≤
      3 * (encodeIndexedOccurrenceEntries (current :: priors)).length + 6 := by
  have hcurrent : current ∈ current :: priors := by simp
  have hfields := entry_fields_le_entries_length hcurrent
  rcases hfields with ⟨hvertex, hclause, hvariable⟩
  exact PricingWithTips3DM_outer_iteration_three_fields
    hclause hvariable hvertex

end CLRS.Chapter34.Turing.TMClique
