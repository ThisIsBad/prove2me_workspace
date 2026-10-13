import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter

namespace AdaptiveStepIPM.Probabilistic

/-- The componentwise identity (18) and lower bound (19). -/
theorem equations_18_19 {n : ℕ} (g w : EuclideanSpace ℝ (Fin n))
    (ζ : ℝ) (hζ : ζ ^ 2 ≤ 1) :
    let η := Real.sqrt (1 - ζ ^ 2)
    let p₀ : Fin n → ℝ := fun j => (1 + ζ) * g j + η * w j
    let q₀ : Fin n → ℝ := fun j => (1 - ζ) * g j - η * w j
    (∀ j : Fin n,
      p₀ j * q₀ j = η ^ 2 * (g j) ^ 2 - 2 * ζ * η * g j * w j - η ^ 2 * (w j) ^ 2 ∧
      p₀ j * q₀ j = -(w j) ^ 2 + (η * g j - ζ * w j) ^ 2 ∧
      -(supNorm w) ^ 2 ≤ p₀ j * q₀ j) ∧
    negSupNorm (fun j => p₀ j * q₀ j) ≤ (supNorm w) ^ 2 := by sorry

end AdaptiveStepIPM.Probabilistic

