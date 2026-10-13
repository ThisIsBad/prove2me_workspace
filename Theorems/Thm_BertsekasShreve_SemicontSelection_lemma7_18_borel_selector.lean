import Mathlib

namespace BertsekasShreve.SemicontSelection

open TopologicalSpace

/-- Lemma 7.18 (Bertsekas & Shreve, p. 151). Let `Y` be a compact metric space. There is a
Borel-measurable `σ : 2^Y − {∅} → Y` with `σ(A) ∈ A` for every nonempty closed `A ⊆ Y`.
Here `2^Y − {∅}` is `NonemptyCompacts Y` (in a compact space the nonempty closed sets are the
nonempty compact sets) with the topology of the Hausdorff metric, and it carries its Borel
σ-algebra. -/
theorem lemma7_18_borel_selector {Y : Type*} [MetricSpace Y] [CompactSpace Y] :
    ∃ σ : NonemptyCompacts Y → Y,
      @Measurable _ _ (borel (NonemptyCompacts Y)) (borel Y) σ ∧ ∀ A : NonemptyCompacts Y, σ A ∈ A := by sorry

end BertsekasShreve.SemicontSelection

