import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem expectation_essSup_eq_iSup {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : ι → Ω → EReal) (hF : ∀ i, AEMeasurable (F i) P)
    (hdir : IsUpwardDirected P F) (hexp : ∀ i, HasExpectation P (F i))
    (i₀ : ι) (hi₀ : negExpectation P (F i₀) ≠ ⊤)
    (Z : Ω → EReal) (hZ : IsEssSup P F Z) :
    HasExpectation P Z ∧ expectation P Z = ⨆ i, expectation P (F i) := by sorry

end CondConvexRisk.Representation
