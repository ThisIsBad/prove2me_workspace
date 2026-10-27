import Definitions.Def_PricingWithTips3DM_a79ce5303af3440f3d4b538fPart1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- First value of one progression: the preceding equality carry wire. -/
noncomputable def transitionEqPreviousForm
    (tm : _root_.Turing.FinTM2)
    (segment : TransitionEqSegment) : AffineUnaryTripleForm :=
  transitionAbsoluteStartForm
    ((transitionEqStartOffsetAffine tm).add
      (segment.publicBase.scale 6))

/-- Third value of one progression: the corresponding next-row source wire. -/
noncomputable def transitionEqNextRowForm
    (tm : _root_.Turing.FinTM2)
    (segment : TransitionEqSegment) : AffineUnaryTripleForm :=
  { constant :=
      (transitionCfgBitAffine tm).constant + segment.publicBase.constant
    first :=
      (transitionCfgBitAffine tm).coefficient +
        segment.publicBase.coefficient
    second := 0
    third := 1 }

/-- Seven runtime values consumed by the generic triple-progression family
controller for one equality segment. -/
noncomputable def transitionEqSegmentDescriptorForms
    (tm : _root_.Turing.FinTM2)
    (segment : TransitionEqSegment) : List AffineUnaryTripleForm :=
  [ transitionEqPreviousForm tm segment,
    transitionFinalMuxWireForm tm
      segment.workspaceBase.constant segment.workspaceBase.coefficient,
    transitionEqNextRowForm tm segment,
    transitionHeightAffineForm (TransitionAffineNat.const 6),
    transitionHeightAffineForm (TransitionAffineNat.const 3),
    transitionHeightAffineForm (TransitionAffineNat.const 1),
    transitionHeightAffineForm segment.count ]

/-- Complete fixed descriptor-form table for one transition row seed. -/
noncomputable def transitionEqProgressionDescriptorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (transitionEqSegments tm).flatMap
    (transitionEqSegmentDescriptorForms tm)

/-- Runtime progression denoted by one segment and one transition row seed. -/
noncomputable def transitionEqSegmentProgression
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment) : AffineUnaryTripleProgression :=
  { base₁ := affineUnaryTripleFormValue
      (transitionEqPreviousForm tm segment) (transitionTailAffineSeed seed)
    base₂ := affineUnaryTripleFormValue
      (transitionFinalMuxWireForm tm
        segment.workspaceBase.constant segment.workspaceBase.coefficient)
      (transitionTailAffineSeed seed)
    base₃ := affineUnaryTripleFormValue
      (transitionEqNextRowForm tm segment) (transitionTailAffineSeed seed)
    step₁ := 6
    step₂ := 3
    step₃ := 1
    count := segment.count.eval seed.height }

/-- Runtime progression family for all public/workspace coordinate segments
of one transition row. -/
noncomputable def transitionEqProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleProgression :=
  (transitionEqSegments tm).map (transitionEqSegmentProgression tm seed)
end CLRS.Chapter34.Turing.CookLevin
