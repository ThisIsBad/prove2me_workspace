import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Proof of Proposition 19, §5.1, p. 876 (Pitman–Yor 1997): "the consequence of (4) that the
`P_{α,θ}` distribution of `(Ṽ₂, Ṽ₃, …)/(1 - Ṽ₁)` is identical to the `P_{α,α+θ}`
distribution of `(Ṽ₁, Ṽ₂, …)`". In the setting of Definition 1 (0-based: `Ytil k` is
`Ỹ_{k+1}`), the sequence `k ↦ PoissonDirichlet.Ratio.stick Ỹ (k+1) / (1 - Ỹ₁)` has the law of `stick` under the
`(α, α + θ)` law of Definition 1, and it is independent of `Ṽ₁ = Ỹ₁` (the independence is
used in the second line of (92)). -/
theorem stick_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (Ytil : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable (Ytil k)) (hYind : iIndepFun Ytil P)
    (hYlaw : ∀ k : ℕ, HasLaw (Ytil k) (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) P) :
    (∃ μ : Measure (ℕ → ℝ), PoissonDirichlet.Ratio.IsStickLaw α (α + θ) μ ∧
        ∀ s : Set (ℕ → ℝ), MeasurableSet s →
          P ((fun ω k => PoissonDirichlet.Ratio.stick (fun i => Ytil i ω) (k + 1) / (1 - Ytil 0 ω)) ⁻¹' s) =
            μ (PoissonDirichlet.Ratio.stick ⁻¹' s)) ∧
      IndepFun (fun ω k => PoissonDirichlet.Ratio.stick (fun i => Ytil i ω) (k + 1) / (1 - Ytil 0 ω))
        (Ytil 0) P := by sorry

end PoissonDirichlet.MaxDensity

