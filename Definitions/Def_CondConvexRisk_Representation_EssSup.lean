import Mathlib

open MeasureTheory

namespace CondConvexRisk.Representation

/-- Appendix A, p. 19: `Z` is an essential supremum of the family `F` of extended random
variables with respect to `P`.  `Z` lies in `D(F)` (it is an a.s. upper bound of every member)
and it is a.s. below every element of `D(F)`.  Elements of `L⁰(ℝ̄)` are represented by
`P`-a.e. measurable functions `Ω → EReal`; every (in)equality is `P`-a.s. -/
def IsEssSup {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ι → Ω → EReal)
    (Z : Ω → EReal) : Prop :=
  AEMeasurable Z P ∧ (∀ i, F i ≤ᵐ[P] Z) ∧
    ∀ W : Ω → EReal, AEMeasurable W P → (∀ i, F i ≤ᵐ[P] W) → Z ≤ᵐ[P] W

/-- Appendix A, p. 19: the family `F` is upward directed, i.e. for any two members there is a
member that is `P`-a.s. above both (equivalently, above their maximum). -/
def IsUpwardDirected {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ι → Ω → EReal) :
    Prop :=
  ∀ i j, ∃ k, F i ≤ᵐ[P] F k ∧ F j ≤ᵐ[P] F k

/-- Positive part `E_P[Z⁺] ∈ [0, +∞]` of an extended random variable. -/
noncomputable def posExpectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → EReal) : ENNReal :=
  ∫⁻ ω, (Z ω).toENNReal ∂P

/-- Negative part `E_P[Z⁻] ∈ [0, +∞]` of an extended random variable. -/
noncomputable def negExpectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → EReal) : ENNReal :=
  ∫⁻ ω, (-Z ω).toENNReal ∂P

/-- The expectation of an extended random variable exists: `E_P[Z⁺]` and `E_P[Z⁻]` are not
both `+∞`. -/
def HasExpectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → EReal) : Prop :=
  posExpectation P Z ≠ ⊤ ∨ negExpectation P Z ≠ ⊤

/-- The (extended) expectation `E_P[Z] = E_P[Z⁺] - E_P[Z⁻] ∈ [-∞, +∞]`.  It is meaningful
only under `HasExpectation P Z` (otherwise `⊤ - ⊤ = ⊥` in `EReal`). -/
noncomputable def expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → EReal) : EReal :=
  (posExpectation P Z : EReal) - (negExpectation P Z : EReal)

end CondConvexRisk.Representation
