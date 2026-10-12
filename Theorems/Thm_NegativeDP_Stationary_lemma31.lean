import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Lemma 3.1, case N (p. 875): `Iₙ(π) ↓ I(π)`, where `Iₙ(π) = Iₙ(π, 0)`. -/
theorem lemma31 (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    Antitone (fun n => In P π n 0 s) ∧
      Tendsto (fun n => In P π n 0 s) atTop (𝓝 (I P π s)) := by sorry

end NegativeDP.Stationary

