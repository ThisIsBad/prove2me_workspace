import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Inequality

/-- **Eq. (11)** (p. 270): by the symmetry of the product measure under permutations `T_i` of
the double sample,
`P{ρ^(l) ≥ ε/2} = ∫ (1/(2l)!) Σ_i θ(ρ^(l)(T_i X_{2l}) − ε/2) dP`, the sum running over all
`(2l)!` permutations; `θ(ρ − ε/2)` is the indicator of `ρ ≥ ε/2`, and `T_i X_{2l}` is
`x ∘ σ`. -/
theorem eq11_permutation_average {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l)) (ε : ℝ) (l : ℕ) :
    Measure.pi (fun _ : Fin (l + l) => P) {x | ε / 2 ≤ Shared.semiSampleDeviation S l x}
      = ENNReal.ofReal (∫ x, ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) =>
            ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ))).card : ℝ) / ((l + l).factorial : ℝ)
          ∂(Measure.pi (fun _ : Fin (l + l) => P))) := by sorry

end VapnikChervonenkis.Inequality
