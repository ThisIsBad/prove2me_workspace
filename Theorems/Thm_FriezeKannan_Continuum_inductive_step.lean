import Mathlib
import Definitions.Def_FriezeKannan_Continuum_Setting

open MeasureTheory

namespace FriezeKannan.Continuum

theorem inductive_step (f : Sq → ℝ) (hf : MemLp f 2)
    (ε : ℝ) (hε : 0 < ε)
    (t : ℕ) (Ss Ts : Fin t → Set unitInterval) (d : Fin t → ℝ)
    (hmS : ∀ j, MeasurableSet (Ss j) ∧ MeasurableSet (Ts j))
    (hinv : l2Norm (fun p => f p - cutFunSum Ss Ts d p) ^ 2
      ≤ (1 - ε ^ 2 * t) * l2Norm f ^ 2) :
    (∀ S T : Set unitInterval, MeasurableSet S → MeasurableSet T →
        |rectInt (fun p => f p - cutFunSum Ss Ts d p) S T| ≤ ε * l2Norm f) ∨
    ∃ (S T : Set unitInterval) (d' : ℝ), MeasurableSet S ∧ MeasurableSet T ∧
      l2Norm (fun p => f p - cutFunSum Ss Ts d p - cutFun S T d' p) ^ 2
        ≤ (1 - ε ^ 2 * (t + 1)) * l2Norm f ^ 2 := by sorry

end FriezeKannan.Continuum

