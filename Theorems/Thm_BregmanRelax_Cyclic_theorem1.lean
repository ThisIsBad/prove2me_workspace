import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions

namespace BregmanRelax.Cyclic

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]

/-- Theorem 1 (Bregman 1967, p. 203): under the cyclic control `n ↦ n mod m` over the `m` sets
`A 0, …, A (m-1)`, every limit point of every relaxation sequence (the limit of a convergent
subsequence) lies in `⋂ i, A i`. -/
theorem theorem1 {m : ℕ} (hm : 0 < m) {A : Fin m → Set X} {S : Set X} {D : X → X → ℝ}
    {P : Fin m → X → X}
    (hA : DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (hV : CondV S D ((⋂ j, A j) ∩ S))
    (x : ℕ → X) (hx : IsRelaxSeq S P (cyclicControl hm) x)
    (x' : X) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Filter.Tendsto (x ∘ φ) Filter.atTop (nhds x')) :
    x' ∈ ⋂ j, A j := by sorry

end BregmanRelax.Cyclic

