import Definitions.Def_PricingWithTips3DM_401d020bee71a0b59916e88f
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! The complete native TM2 computing the fixed-shape SAT-to-3DM encoding. -/

noncomputable section

namespace PricingWithTips.FixedShapeReductionTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing.PolyBuilder
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeEncoding
open PricingWithTips.FixedShapeBaselineTM2
open PricingWithTips.FixedShapeDenseTableTM2
open PricingWithTips.FixedShapeDenseTableSemantics

def encodedReduction (input : List CNFSym) : List Bool :=
  prefixBits input ++ denseBits input

theorem encodedReduction_eq (input : List CNFSym) :
    encodedReduction input = encodeThreeDMInstance (reduction input) := by
  rw [encodedReduction, prefixBits_eq, denseBits_eq_table,
    encode_reduction_eq]

noncomputable def encodedReduction_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id encodedReduction :=
  fixedPairSameInputConcat_computableInPolyTime
    boolPairEncode boolPairDecode boolPair_leftInverse
    (by
      let frames :=
        exactPolynomialUnaryFrame_computableInPolyTime
          (Γ := CNFSym) dimensionPolynomial
      exact Classical.choice (Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
        frames (boundedLoop_computableInPolyTime prefixBitBody)))
    denseBits_computableInPolyTime

noncomputable def reduction_computableInPolyTime :
    Turing.TM2ComputableInPolyTime
      (id : List CNFSym → List CNFSym)
      encodeThreeDMInstance reduction := by
  let machine := encodedReduction_computableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [encodedReduction_eq] using output }

theorem threeDM_np_hard : NPHardMarketPredicate ThreeDMYes :=
  FixedShape3DM.threeDM_np_hard_of_reduction_polytime
    ⟨reduction_computableInPolyTime⟩

end PricingWithTips.FixedShapeReductionTM2
