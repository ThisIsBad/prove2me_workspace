import Mathlib

open MeasureTheory

namespace CondConvexRisk.Representation

/-- Section 2, p. 3: the set `P_G` of probability measures `Q` on `(Ω, F)` with `Q ≪ P` on `F`
and `Q ≡ P` on `G`, i.e. `Q(A) = P(A)` for every `A ∈ G`.  Here `F` is the ambient σ-algebra
`mΩ` and `G` is the sub-σ-algebra `m`. -/
def PG {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) :
    Type _ :=
  {Q : Measure[mΩ] Ω // IsProbabilityMeasure Q ∧ Q ≪ P ∧ ∀ A, MeasurableSet[m] A → Q A = P A}

/-- Definition 2.2, p. 4 (with the three axioms of p. 3): `ρ : L∞ → L∞_G` is a conditional
convex risk measure.  Payoffs are real functions with `MemLp X ∞ P`; `ρ` acts on functions, so
it is required to respect `P`-a.s. equality (the paper works on equivalence classes), and its
value on each `X ∈ L∞` is a `G`-measurable essentially bounded function.  All (in)equalities
between random variables are `P`-a.s.  `ρ` is unconstrained outside `L∞`. -/
structure IsCondConvexRiskMeasure {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ρ : (Ω → ℝ) → Ω → ℝ) : Prop where
  /-- `ρ` is well defined on `P`-equivalence classes. -/
  ae_congr : ∀ X Y : Ω → ℝ, MemLp X ⊤ P → MemLp Y ⊤ P → X =ᵐ[P] Y → ρ X =ᵐ[P] ρ Y
  /-- `ρ(X)` is `G`-measurable. -/
  stronglyMeasurable : ∀ X : Ω → ℝ, MemLp X ⊤ P → StronglyMeasurable[m] (ρ X)
  /-- `ρ(X)` is essentially bounded. -/
  memLp : ∀ X : Ω → ℝ, MemLp X ⊤ P → MemLp (ρ X) ⊤ P
  /-- (Conditional) translation invariance: `ρ(X + Z) = ρ(X) - Z` for `Z ∈ L∞_G`. -/
  translation : ∀ X Z : Ω → ℝ, MemLp X ⊤ P → MemLp Z ⊤ P → StronglyMeasurable[m] Z →
    ρ (X + Z) =ᵐ[P] ρ X - Z
  /-- Monotonicity: `X ≤ Y` implies `ρ(X) ≥ ρ(Y)`. -/
  monotone : ∀ X Y : Ω → ℝ, MemLp X ⊤ P → MemLp Y ⊤ P → X ≤ᵐ[P] Y → ρ Y ≤ᵐ[P] ρ X
  /-- (Conditional) convexity with `G`-measurable weights `0 ≤ Λ ≤ 1`. -/
  convex : ∀ X Y Λ : Ω → ℝ, MemLp X ⊤ P → MemLp Y ⊤ P → StronglyMeasurable[m] Λ →
    (∀ᵐ ω ∂P, 0 ≤ Λ ω ∧ Λ ω ≤ 1) →
    ρ (Λ * X + (1 - Λ) * Y) ≤ᵐ[P] Λ * ρ X + (1 - Λ) * ρ Y
  /-- Normalization: `ρ(0) = 0`. -/
  map_zero : ρ 0 =ᵐ[P] 0

end CondConvexRisk.Representation
