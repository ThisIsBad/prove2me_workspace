import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model

namespace NegativeDP.OptEq

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- `(p, ε)`-optimality (p. 875): `p{NegativeDP.Stationary.I(π) ≥ v* − ε} = 1`, read in the completion of `p`. -/
def IsPEOptimal (P : NegativeDP.Stationary.Problem S A) (p : Measure S) (ε : ℝ) (π : Plan (S := S) (A := A)) :
    Prop :=
  IsProbabilityMeasure p ∧
    ∀ᵐ s ∂p, NegativeDP.Stationary.vstar P s - (ε : EReal) ≤ NegativeDP.Stationary.I P π s

/-- `T_a`, the operator of the constant rule `f ≡ a` (p. 885). -/
noncomputable def Ta (P : NegativeDP.Stationary.Problem S A) (a : A) (u : S → EReal) (s : S) : EReal :=
  -((∫⁻ t, ENNReal.ofReal (-P.r (s, a, t)) + (-(u t)).toENNReal ∂P.q (s, a) : ℝ≥0∞) : EReal)

/-- The operator of a Markov plan `π = (f₁, f₂, …)` (p. 879): `Uu = supₙ Tₙu`. -/
noncomputable def U (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : S → EReal) (s : S) : EReal :=
  ⨆ n : ℕ, NegativeDP.Stationary.T P (π n) u s

/-- `U` conserves `v ∈ M(S)` if `Uv ≥ v` (p. 881). -/
def Conserves (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (v : S → EReal) : Prop :=
  NegativeDP.Stationary.IsNegM v ∧ ∀ s, v s ≤ U P π v s

/-- `u` is excessive for `U` if `Uu ≤ u` (p. 883); `u ∈ M(S)` is stated separately. -/
def IsExcessive (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : S → EReal) : Prop :=
  ∀ s, U P π u s ≤ u s

/-- `ⁿπ = (fₙ₊₁, fₙ₊₂, …)` for a Markov plan `π = (f₁, f₂, …)` (p. 874). -/
def shift (π : MarkovPlan S A) (n : ℕ) : MarkovPlan S A := fun k => π (k + n)

end NegativeDP.OptEq
