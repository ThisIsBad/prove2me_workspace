import Mathlib
import Definitions.Def_PoissonDirichlet_Ratio_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Ratio

/-- The Poisson-arrival ratio claim in the proof of Proposition 8, p. 870. -/
theorem poisson_ratio_beta {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ)
    (hind : iIndepFun ε P)
    (hlaw : ∀ i : ℕ, HasLaw (ε i) (expMeasure 1) P) :
    let X : Ω → ℕ → ℝ := fun ω k =>
      ∑ i ∈ Finset.range (k + 1), ε i ω
    iIndepFun (fun k ω => X ω k / X ω (k + 1)) P ∧
      ∀ k : ℕ, HasLaw (fun ω => X ω k / X ω (k + 1))
        (betaMeasure ((k : ℝ) + 1) 1) P := by sorry

end PoissonDirichlet.Ratio

