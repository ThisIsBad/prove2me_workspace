import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions

namespace BregmanRelax.Cyclic

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]

/-- Lemma 2 (2) (Bregman 1967, p. 202): for any relaxation control and any `z ∈ R ∩ S`,
where `R = ⋂ j, A j`, the limit `lim_{n→∞} D z (x n)` exists. -/
theorem lemma2_limit {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : DConditions A S D P)
    (i : ℕ → ι) (x : ℕ → X) (hx : IsRelaxSeq S P i x)
    (z : X) (hz : z ∈ (⋂ j, A j) ∩ S) :
    ∃ c : ℝ, Filter.Tendsto (fun n => D z (x n)) Filter.atTop (nhds c) := by sorry

end BregmanRelax.Cyclic

