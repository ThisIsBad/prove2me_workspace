import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Display (92), p. 876 (Pitman–Yor 1997), proof of Proposition 19, first and last
expression. In the setting of Definition 1 (`Ṽ = PoissonDirichlet.Ratio.stick Ỹ`, `V` its PoissonDirichlet.Ratio.ranked values), and with
`V'` a sequence with `PD(α, α + θ)` distribution on another probability space `(Ω', P')`,
`P(V₁ ∈ dx, V₁ = Ṽ₁) = Γ(θ+1)/(Γ(θ+α)Γ(1-α)) x^{-α}(1-x)^{α+θ-1} P'(V'₁ < x/(1-x)) dx`
on `(0, 1)`. -/
theorem eq_92 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (Ytil : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable (Ytil k)) (hYind : iIndepFun Ytil P)
    (hYlaw : ∀ k : ℕ, HasLaw (Ytil k) (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) P)
    (V' : Ω' → ℕ → ℝ) (hV' : PoissonDirichlet.Ratio.HasPD α (α + θ) P' V')
    (s : Set ℝ) (hs : MeasurableSet s) :
    P {ω | PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) 0 ∈ s ∧
        PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) 0 = PoissonDirichlet.Ratio.stick (fun k => Ytil k ω) 0} =
      ∫⁻ x in s ∩ Set.Ioo (0 : ℝ) 1, ENNReal.ofReal
        (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
          * x ^ (-α) * (1 - x) ^ (α + θ - 1)
          * (P' {ω' | V' ω' 0 < x / (1 - x)}).toReal) := by sorry

end PoissonDirichlet.MaxDensity

