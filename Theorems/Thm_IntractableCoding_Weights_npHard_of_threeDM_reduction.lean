import Mathlib
import Definitions.Def_IntractableCoding_Weights_NPComplete

namespace IntractableCoding.Weights

open PricingWithTips

/-- NP-hardness transfers along a polynomial-time many-one reduction from
THREE-DIMENSIONAL MATCHING: if a map `g` from 3DM instances to instances of `P`, computed by a
polynomial-time TM2 machine from `encodeThreeDMInstance I` to `enc (g I)`, satisfies
`ThreeDMYes I ↔ P (g I)` for every `I`, then `P` is NP-hard (with respect to `enc`). -/
theorem npHard_of_threeDM_reduction {α : Type} (enc : α → List Bool) (P : α → Prop)
    (g : ThreeDMInstance → α)
    (hg : Nonempty (Turing.TM2ComputableInPolyTime encodeThreeDMInstance enc g))
    (hred : ∀ I : ThreeDMInstance, ThreeDMYes I ↔ P (g I)) :
    NPHardFor enc P := by sorry

end IntractableCoding.Weights

