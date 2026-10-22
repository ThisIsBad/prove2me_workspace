import Mathlib
import Definitions.Def_FriezeKannan_Continuum_Setting

open MeasureTheory

namespace FriezeKannan.Continuum

theorem l2_drop_le (f w : Sq → ℝ) (hw : MemLp w 2) (ε : ℝ) (hε : 0 < ε)
    (S T : Set unitInterval) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (h : ε * l2Norm f < |rectInt w S T|) :
    let d := rectInt w S T / ((volume S).toReal * (volume T).toReal)
    l2Norm (fun p => w p - cutFun S T d p) ^ 2 - l2Norm w ^ 2 ≤ -ε ^ 2 * l2Norm f ^ 2 := by sorry

end FriezeKannan.Continuum

