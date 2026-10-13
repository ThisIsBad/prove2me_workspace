import Mathlib

namespace BertsekasShreve.AnalyticSelection

open MeasureTheory

universe u

/-- **Definition 7.7** (Bertsekas–Shreve, p. 118). A topological space `X` is a *Borel space* if
it is homeomorphic to a Borel subset `B` of some complete separable metric space `Z`. (The empty
space is covered: it is homeomorphic to `∅ ⊆ Z`.) The ambient space `Z` is taken in the universe
of `X`. This is a property of the topology only; theorems additionally equip `X` with its Borel
σ-algebra through Mathlib's `[MeasurableSpace X] [BorelSpace X]`. -/
class IsBorelSpace (X : Type u) [TopologicalSpace X] : Prop where
  exists_homeomorph_borel :
    ∃ (Z : Type u) (_ : MetricSpace Z) (_ : CompleteSpace Z)
      (_ : TopologicalSpace.SeparableSpace Z) (B : Set Z),
      MeasurableSet[borel Z] B ∧ Nonempty (X ≃ₜ B)

end BertsekasShreve.AnalyticSelection
