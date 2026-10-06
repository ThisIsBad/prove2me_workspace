import Mathlib
import Definitions.Def_BregmanRelax_Remotest_DConditions

namespace BregmanRelax.Remotest

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Theorem 2 (Bregman 1967, p. 203): if at every step the control chooses an index realizing
`max_j D (P j (x n)) (x n)` (the remotest set in the sense of `D`), then every limit point of
the relaxation sequence (the limit of a convergent subsequence) lies in `⋂ j, A j`. The index
set `ι` is arbitrary (possibly infinite). -/
theorem theorem2 {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (hV : BregmanRelax.Cyclic.CondV S D ((⋂ j, A j) ∩ S))
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x) (hi : IsRemotestControl D P i x)
    (x' : X) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Filter.Tendsto (x ∘ φ) Filter.atTop (nhds x')) :
    x' ∈ ⋂ j, A j := by sorry

end BregmanRelax.Remotest

