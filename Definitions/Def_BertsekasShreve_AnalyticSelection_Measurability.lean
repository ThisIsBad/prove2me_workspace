import Mathlib

namespace BertsekasShreve.AnalyticSelection

open MeasureTheory

/-- **Definition 7.18** (p. 167). A set `E ⊆ X` is *universally measurable* if it belongs to the
completion `𝓑_X(p)` of the Borel σ-algebra with respect to every probability measure `p` on `X`,
i.e. it is `p`-null-measurable for every probability measure `p`. -/
def IsUniversallyMeasurable {X : Type*} [MeasurableSpace X] (E : Set X) : Prop :=
  ∀ p : Measure X, IsProbabilityMeasure p → NullMeasurableSet E p

set_option warn.classDefReducibility false in
/-- **Definition 7.19** (p. 171). The *analytic σ-algebra* `𝒜_X`: the smallest σ-algebra
containing the analytic subsets of `X` (analytic sets in the sense of Mathlib's `AnalyticSet`:
empty or a continuous image of the Baire space `ℕ → ℕ`, the book's Proposition 7.41(c)). -/
def analyticSigmaAlgebra (X : Type*) [TopologicalSpace X] : MeasurableSpace X :=
  MeasurableSpace.generateFrom {A : Set X | AnalyticSet A}

/-- **Definition 7.19** (p. 171). `E` is *analytically measurable* if `E ∈ 𝒜_X`. -/
def IsAnalyticallyMeasurable {X : Type*} [TopologicalSpace X] (E : Set X) : Prop :=
  MeasurableSet[analyticSigmaAlgebra X] E

/-- **Definition 7.20** (p. 171). A function `f : D → Y` defined on a subset `D ⊆ X` is
*analytically measurable* if `D ∈ 𝒜_X` and `f⁻¹(B) ∈ 𝒜_X` for every Borel set `B ⊆ Y`. -/
def IsAnalyticallyMeasurableFun {X Y : Type*} [TopologicalSpace X] [MeasurableSpace Y]
    (D : Set X) (f : D → Y) : Prop :=
  IsAnalyticallyMeasurable D ∧
    ∀ B : Set Y, MeasurableSet B → IsAnalyticallyMeasurable (Subtype.val '' (f ⁻¹' B))

/-- **Definition 7.20** (p. 171). A function `f : D → Y` defined on a subset `D ⊆ X` is
*universally measurable* if `D ∈ 𝒰_X` and `f⁻¹(B) ∈ 𝒰_X` for every Borel set `B ⊆ Y`. -/
def IsUniversallyMeasurableFun {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Set X) (f : D → Y) : Prop :=
  IsUniversallyMeasurable D ∧
    ∀ B : Set Y, MeasurableSet B → IsUniversallyMeasurable (Subtype.val '' (f ⁻¹' B))

end BertsekasShreve.AnalyticSelection
