import Mathlib

open MeasureTheory Filter Topology

namespace CondConvexRisk.Entropic

/-- Section 2, p. 3: the set `P_G` of probability measures `Q` on `(Ω, F)` with `Q ≪ P` on `F`
and `Q ≡ P` on `G`, i.e. `Q(A) = P(A)` for every `A ∈ G`.  Here `F` is the ambient σ-algebra
`mΩ` and `G` is the sub-σ-algebra `m`. -/
def PG {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) :
    Type _ :=
  {Q : Measure[mΩ] Ω // IsProbabilityMeasure Q ∧ Q ≪ P ∧ ∀ A, MeasurableSet[m] A → Q A = P A}

/-- The space `L∞` of payoffs, as the subtype of real functions with `MemLp X ∞ P`. -/
abbrev LInf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) : Type _ :=
  {X : Ω → ℝ // MemLp X ⊤ P}

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

/-- Appendix A, p. 19: `Z` is an essential supremum of the family `F` of extended random
variables with respect to `P`: `Z` is an a.s. upper bound of every member, and it is a.s. below
every (a.e.-measurable) a.s. upper bound of the family.  Elements of `L⁰(ℝ̄)` are represented by
`P`-a.e. measurable functions `Ω → EReal`; every (in)equality is `P`-a.s. -/
def IsEssSup {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ι → Ω → EReal)
    (Z : Ω → EReal) : Prop :=
  AEMeasurable Z P ∧ (∀ i, F i ≤ᵐ[P] Z) ∧
    ∀ W : Ω → EReal, AEMeasurable W P → (∀ i, F i ≤ᵐ[P] W) → Z ≤ᵐ[P] W

/-- Appendix A, p. 19: `Z` is an essential infimum of the family `F`
(`ess.inf 𝒳 = -ess.sup(-𝒳)`, written out): `Z` is an a.s. lower bound of every member, and it
is a.s. above every (a.e.-measurable) a.s. lower bound of the family. -/
def IsEssInf {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ι → Ω → EReal)
    (Z : Ω → EReal) : Prop :=
  AEMeasurable Z P ∧ (∀ i, Z ≤ᵐ[P] F i) ∧
    ∀ W : Ω → EReal, AEMeasurable W P → (∀ i, W ≤ᵐ[P] F i) → W ≤ᵐ[P] Z

/-- Theorem 3.2 (a), p. 6: `ρ` is continuous from above: whenever `X_n, X ∈ L∞` and
`X_n ↘ X` `P`-a.s. (a.s. non-increasing and a.s. convergent to `X`), then `ρ(X_n) ↗ ρ(X)`
`P`-a.s. (a.s. non-decreasing and a.s. convergent to `ρ(X)`). -/
def IsContinuousFromAbove {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ : (Ω → ℝ) → Ω → ℝ) : Prop :=
  ∀ (X : ℕ → Ω → ℝ) (Y : Ω → ℝ), (∀ n, MemLp (X n) ⊤ P) → MemLp Y ⊤ P →
    (∀ᵐ ω ∂P, Antitone (fun n => X n ω) ∧ Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) →
    ∀ᵐ ω ∂P, Monotone (fun n => ρ (X n) ω) ∧ Tendsto (fun n => ρ (X n) ω) atTop (𝓝 (ρ Y ω))

/-- The family `{-E_Q(X | G) - ρ(X) | X ∈ L∞}` (p. 7), indexed by `X ∈ L∞`, whose essential
supremum is the minimal penalty `α*(Q)` of Theorem 3.2 (c), p. 6.  `E_Q(X | G)` is Mathlib's
conditional expectation `Q[X | m]` (well defined: `X` is `Q`-integrable since `Q ≪ P`). -/
noncomputable def penaltyFamily {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ρ : (Ω → ℝ) → Ω → ℝ) (Q : PG m P) : LInf P → Ω → EReal :=
  fun X ω => ((-(Q.1[X.1 | m]) ω - ρ X.1 ω : ℝ) : EReal)

/-- Theorem 3.2 (c), p. 6: `α*` is the minimal penalty of `ρ`,
`α*(Q) = ess.sup_{X ∈ L∞} {-E_Q(X | G) - ρ(X)}` for every `Q ∈ P_G`.  A predicate on a
candidate `α*`. -/
def IsMinimalPenalty {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ρ : (Ω → ℝ) → Ω → ℝ) (α : PG m P → Ω → EReal) : Prop :=
  ∀ Q : PG m P, IsEssSup P (penaltyFamily m P ρ Q) (α Q)

end CondConvexRisk.Entropic
