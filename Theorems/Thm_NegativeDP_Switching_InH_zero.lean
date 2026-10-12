import Mathlib
import Definitions.Def_NegativeDP_Switching_Model
open MeasureTheory ProbabilityTheory
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

namespace NegativeDP.Switching

/-- Proof of Theorem 9.3 (p. 888): `I_0(π, w_1) = w_1 = max(I(σ), I(τ))`, for every plan `π`. -/
theorem InH_zero {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (σ τ π : Plan (S := S) (A := A)) (s : S) :
    InH P π 0 (wmax P σ τ 0) s = wmax P σ τ 0 (Hist.start s) ∧
    wmax P σ τ 0 (Hist.start s) = max (I P σ s) (I P τ s) := by sorry
end NegativeDP.Switching

