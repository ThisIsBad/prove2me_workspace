import Definitions.Def_PricingWithTips3DM_5ec6efe3c13ebba9e8487e8d
import Definitions.Def_PricingWithTips3DM_12d2e8cf841ea25263d0c142
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Raw-input source for final transition constraint wires

The transition outputs form a second exact polynomial affine progression,
starting at the completed-validity endpoint.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- First final-conjunction transition source wire. -/
def verifierTransitionOutputBasePolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  verifierTransitionStartPolynomial W +
    verifierTransitionOutputOffsetPolynomial W

/-- Forward delimiter-bearing transition source blocks. -/
def verifierTransitionOutputSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    (verifierTransitionOutputBasePolynomial W)
    (verifierTransitionCostPolynomial W)
    (verifierHorizon W) input

/-- The affine source is exactly the semantic transition-output list. -/
theorem verifierTransitionOutputSource_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionOutputSource W input =
      encodeAffineConjunctionSources
        (List.ofFn (verifierTransitions W input).outputs) := by
  unfold verifierTransitionOutputSource
    exactPolynomialAffineUnaryProgressionFrameStream
    affineUnaryProgressionFrameStream affineUnaryProgressionValues
    exactPolynomialAffineUnaryProgression
  rw [affineUnaryProgressionValuesFrom_eq_ofFn]
  simp only [verifierTransitionOutputBasePolynomial,
    Polynomial.eval_add, verifierTransitionCostPolynomial_eval]
  unfold encodeAffineConjunctionSources encodeUnaryFrame
  congr 1
  apply List.ofFn_inj.mpr
  funext step
  rw [verifierTransitions_output_eq]
  ring

/-- A fixed polynomial-time TM2 emits every transition output source from the
original verifier word. -/
noncomputable def verifierTransitionOutputSource_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionOutputSource W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact
    exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
      (verifierTransitionOutputBasePolynomial W)
      (verifierTransitionCostPolynomial W)
      (verifierHorizon W)

end CLRS.Chapter34.Turing.CookLevin
