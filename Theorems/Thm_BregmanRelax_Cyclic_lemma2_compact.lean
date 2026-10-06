import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions

namespace BregmanRelax.Cyclic

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]

/-- Lemma 2 (1) (Bregman 1967, p. 202): for any relaxation control, the set of elements of the
relaxation sequence lies in a sequentially compact set. -/
theorem lemma2_compact {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (hV : CondV S D ((⋂ j, A j) ∩ S))
    (i : ℕ → ι) (x : ℕ → X) (hx : IsRelaxSeq S P i x) :
    ∃ K : Set X, IsSeqCompact K ∧ ∀ n, x n ∈ K := by sorry

end BregmanRelax.Cyclic

