import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.OptEq

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Strauch (1966), Theorem 5.2(a), p. 879, negative case: `U` is monotone on `M(S)`. -/
theorem theorem52a (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u v : S → EReal)
    (hu : NegativeDP.Stationary.IsNegM u) (hv : NegativeDP.Stationary.IsNegM v) (huv : ∀ s, u s ≤ v s) :
    ∀ s, U P π u s ≤ U P π v s := by sorry

end NegativeDP.OptEq

