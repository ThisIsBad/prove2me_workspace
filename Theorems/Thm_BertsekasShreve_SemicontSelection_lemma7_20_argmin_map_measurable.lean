import Mathlib

namespace BertsekasShreve.SemicontSelection

open TopologicalSpace

/-- Lemma 7.20 (Bertsekas & Shreve, p. 152). Let `X` be metrizable, `Y` a nonempty compact metric space,
`f : X × Y → R*` lower semicontinuous, `f*(x) = min_{y ∈ Y} f(x, y)`, and
`F*(x) = {y ∈ Y | f(x, y) ≤ f*(x)}` (Eq. (64) of Chapter 7). Then `F* : X → 2^Y` is
Borel-measurable, where `2^Y` is the space of closed subsets of `Y` with the Hausdorff-metric
topology and its Borel σ-algebra. The statement asserts that each `F*(x)` is a closed set (so `F*`
is a map into `2^Y`) and that this map is Borel-measurable. -/
theorem lemma7_20_argmin_map_measurable {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (f : X × Y → EReal) (hf : LowerSemicontinuous f) :
    ∃ F : X → Closeds Y, (∀ x, (F x : Set Y) = {y | f (x, y) ≤ ⨅ y', f (x, y')}) ∧
      @Measurable _ _ (borel X) (borel (Closeds Y)) F := by sorry

end BertsekasShreve.SemicontSelection

