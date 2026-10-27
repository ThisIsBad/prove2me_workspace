import Definitions.Def_PricingWithTips3DM_a79ce5303af3440f3d4b538fPart3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The fixed seven-form block is byte-for-byte the canonical descriptor of
the runtime progression it denotes. -/
theorem transitionEqSegmentDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment) :
    affineUnaryTripleMap (transitionEqSegmentDescriptorForms tm segment)
        (transitionTailAffineSeed seed) =
      [ (transitionEqSegmentProgression tm seed segment).base₁,
        (transitionEqSegmentProgression tm seed segment).base₂,
        (transitionEqSegmentProgression tm seed segment).base₃,
        (transitionEqSegmentProgression tm seed segment).step₁,
        (transitionEqSegmentProgression tm seed segment).step₂,
        (transitionEqSegmentProgression tm seed segment).step₃,
        (transitionEqSegmentProgression tm seed segment).count ] := by
  simp [transitionEqSegmentDescriptorForms,
    transitionEqSegmentProgression, affineUnaryTripleMap]

/-- Evaluating the complete fixed form table yields exactly the concatenated
runtime progression descriptors for one row. -/
theorem transitionEqProgressionDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap (transitionEqProgressionDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      (transitionEqProgressions tm seed).flatMap fun progression =>
        [progression.base₁, progression.base₂, progression.base₃,
          progression.step₁, progression.step₂, progression.step₃,
          progression.count] := by
  unfold transitionEqProgressionDescriptorForms transitionEqProgressions
    affineUnaryTripleMap
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro segment _
  exact transitionEqSegmentDescriptorForms_value tm seed segment

/-- The descriptor bytes for one row are exactly the generic progression
family encoding, not merely a list with the same decoded values. -/
theorem encode_transitionEqProgressionDescriptorForms
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    encodeUnaryFrame
        (affineUnaryTripleMap (transitionEqProgressionDescriptorForms tm)
          (transitionTailAffineSeed seed)) =
      encodeAffineUnaryTripleProgressionFamily
        (transitionEqProgressions tm seed) := by
  rw [transitionEqProgressionDescriptorForms_value]
  unfold encodeUnaryFrame
  induction transitionEqProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [List.flatMap_cons,
        encodeAffineUnaryTripleProgressionFamily,
        encodeAffineUnaryTripleProgression, List.flatMap_append]
      rw [ih]
      simp [encodeUnaryFrame, List.append_assoc]
end CLRS.Chapter34.Turing.CookLevin
