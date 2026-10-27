import Mathlib
import Definitions.Def_PricingWithTips_NPHardness

namespace IntractableCoding.Weights

/-- The language of an encoded decision problem: the binary strings that encode some
yes-instance. Strings that encode no instance at all are not in the language. -/
def languageOf {α : Type} (enc : α → List Bool) (P : α → Prop) : Set (List Bool) :=
  {s | ∃ a, enc a = s ∧ P a}

/-- NP-hardness of a decision problem `P` on instances `α`, presented to machines through the
binary encoding `enc`: every polynomially verifiable language `L` over every alphabet `Γ`
(`PricingWithTips.PolynomiallyVerifiable`, a polynomial-time TM2 verifier with polynomially
long certificates) many-one reduces to `P` by a map `f` computed by a polynomial-time TM2
machine from the input string to the encoding `enc (f x)` of the produced instance.
For `α = ThreeDMInstance` and `enc = encodeThreeDMInstance` this is literally
`PricingWithTips.NPHardMarketPredicate`. -/
def NPHardFor {α : Type} (enc : α → List Bool) (P : α → Prop) : Prop :=
  ∀ (Γ : Type) (L : Set (List Γ)), PricingWithTips.PolynomiallyVerifiable L →
    ∃ f : List Γ → α,
      Nonempty (Turing.TM2ComputableInPolyTime (id : List Γ → List Γ) enc f) ∧
      ∀ x : List Γ, x ∈ L ↔ P (f x)

/-- NP-completeness of an encoded decision problem: its language is in NP and it is NP-hard
under polynomial-time many-one reductions. -/
def NPCompleteFor {α : Type} (enc : α → List Bool) (P : α → Prop) : Prop :=
  PricingWithTips.PolynomiallyVerifiable (languageOf enc P) ∧ NPHardFor enc P

end IntractableCoding.Weights
