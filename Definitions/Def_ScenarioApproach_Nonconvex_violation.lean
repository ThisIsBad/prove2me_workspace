import Mathlib

namespace ScenarioApproach.Nonconvex

/-- Definition 3.1 (violation set), over a generic decision set `Θ`. The violation set of a
decision `θ` is the set of uncertainty instances `δ` whose constraint `Θδ δ` does not
contain `θ`. -/
def violationSet {Θ Δ : Type*} (Θδ : Δ → Set Θ) (θ : Θ) : Set Δ :=
  {δ | θ ∉ Θδ δ}

/-- Definition 3.1 (violation probability). `V(θ) := ℙ{δ ∈ Δ : θ ∉ Θ_δ}`, as a real number;
for a probability measure `P` it lies in `[0, 1]`. -/
noncomputable def violation {Θ Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) (Θδ : Δ → Set Θ) (θ : Θ) : ℝ :=
  (P (violationSet Θδ θ)).toReal

end ScenarioApproach.Nonconvex
