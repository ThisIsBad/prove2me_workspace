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

/-- Strauch (1966), Theorem 5.2(c), p. 879, negative case: `U(supⱼ uⱼ) ≥ supⱼ Uuⱼ` for a
sequence `u₁, u₂, …` in `M(S)`. -/
theorem theorem52c (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : ℕ → S → EReal)
    (hu : ∀ j, NegativeDP.Stationary.IsNegM (u j)) :
    ∀ s, ⨆ j, U P π (u j) s ≤ U P π (fun t => ⨆ j, u j t) s := by sorry

end NegativeDP.OptEq

