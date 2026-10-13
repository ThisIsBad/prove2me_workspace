import Mathlib

namespace ScenarioApproach.Generalization

/-- Definition 3.1 (violation set). The violation set of a decision `θ` is the set of
uncertainty instances `δ` whose constraint `Θδ δ` does not contain `θ`. -/
def violationSet {d : ℕ} {Δ : Type*} (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (θ : EuclideanSpace ℝ (Fin d)) : Set Δ :=
  {δ | θ ∉ Θδ δ}

/-- Definition 3.1 (violation probability). `V(θ) := ℙ{δ ∈ Δ : θ ∉ Θ_δ}`, as a real number;
for a probability measure `P` it lies in `[0, 1]`. -/
noncomputable def violation {d : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (P (violationSet Θδ θ)).toReal

end ScenarioApproach.Generalization
