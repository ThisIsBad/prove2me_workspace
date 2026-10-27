import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem outer_iterations_steps_le_mul
    (entries : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesOuterIterationsSteps entries ≤
      entries.length *
        (70 * ((encodeIndexedOccurrenceEntries entries).length + 1) ^ 2) := by
  induction entries with
  | nil => simp [compatibilityEdgesOuterIterationsSteps]
  | cons current priors ih =>
      have hfirst := outer_iteration_steps_le current priors
      have hencoding :
          (encodeIndexedOccurrenceEntries priors).length ≤
            (encodeIndexedOccurrenceEntries (current :: priors)).length := by
        simp [encodeIndexedOccurrenceEntries]
      have hpow :
          ((encodeIndexedOccurrenceEntries priors).length + 1) ^ 2 ≤
            ((encodeIndexedOccurrenceEntries (current :: priors)).length + 1) ^ 2 :=
        Nat.pow_le_pow_left (Nat.add_le_add_right hencoding 1) 2
      have hrest : compatibilityEdgesOuterIterationsSteps priors ≤
          priors.length *
            (70 * ((encodeIndexedOccurrenceEntries
              (current :: priors)).length + 1) ^ 2) :=
        ih.trans (Nat.mul_le_mul_left priors.length
          (Nat.mul_le_mul_left 70 hpow))
      simp only [compatibilityEdgesOuterIterationsSteps, List.length_cons]
      nlinarith
end CLRS.Chapter34.Turing.TMClique
