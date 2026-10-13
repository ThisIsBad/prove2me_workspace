import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability

open MeasureTheory

namespace BertsekasShreve.AnalyticSelection

/-- **Corollary 7.44.2** (p. 172). Let `X`, `Y`, `Z` be Borel spaces, `D ∈ 𝒜_X`, `E ∈ 𝒜_Y`, and
`f : D → Y`, `g : E → Z` analytically measurable with `f(D) ⊆ E`. Then `g ∘ f` is universally
measurable, and `f⁻¹(A) ∈ 𝒰_X` for every `A ∈ 𝒜_Y`. -/
theorem comp_analyticallyMeasurable {X Y Z : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [IsBorelSpace Z]
    (D : Set X) (E : Set Y) (hD : IsAnalyticallyMeasurable D) (hE : IsAnalyticallyMeasurable E)
    (f : D → Y) (g : E → Z)
    (hf : IsAnalyticallyMeasurableFun D f) (hg : IsAnalyticallyMeasurableFun E g)
    (hfE : ∀ x : D, f x ∈ E) :
    IsUniversallyMeasurableFun D (fun x : D => g ⟨f x, hfE x⟩) ∧
    ∀ A : Set Y, IsAnalyticallyMeasurable A →
      IsUniversallyMeasurable (Subtype.val '' (f ⁻¹' A)) := by sorry

end BertsekasShreve.AnalyticSelection

