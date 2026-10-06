import Mathlib
import Definitions.Def_BregmanRelax_Remotest_DConditions

namespace BregmanRelax.Remotest

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Lemma 2 (3) (Bregman 1967, p. 202): for any relaxation control,
`D (x (n+1)) (x n) → 0`. -/
theorem lemma2_step {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x) :
    Filter.Tendsto (fun n => D (x (n + 1)) (x n)) Filter.atTop (nhds 0) := by sorry

end BregmanRelax.Remotest

