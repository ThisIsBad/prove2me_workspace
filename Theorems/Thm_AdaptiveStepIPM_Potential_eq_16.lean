import Mathlib
import Definitions.Def_LinearOptimization_InteriorPointPotential
import Definitions.Def_AdaptiveStepIPM_Potential_Algorithm3

open Matrix

namespace AdaptiveStepIPM.Potential

/-- **(16), proof of Theorem 3, p. 12.** Let `β, γ ∈ (0, 1)` with `γ ≤ 2(1 − β)`,
`ρ = n + (3/(βγ(1 − γ)) log(1/(1 − β))) n²`, `(x, s) ∈ N_∞⁻(β)`, `d` a solution of (2) at
`(x, s)` with `γ`, and `θ̄` an Algorithm 3 step: `(x(θ̄), s(θ̄)) ∈ N_∞⁻(β)` and `θ̄` minimises
`ψ(x(θ), s(θ))` over all `θ` with `(x(θ), s(θ)) ∈ N_∞⁻(β)`. Then
`ψ(x(θ̄), s(θ̄)) − ψ(x, s) ≤ −(3n²θ₂⁻/(βγ) − n) log(1/(1 − β))`. -/
theorem eq_16 {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (x s : Fin n → ℝ) (hN : InNinfMinus A b c β x s)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsNewtonDirection A γ x s dx dy ds) (θbar : ℝ)
    (hθN : InNinfMinus A b c β (lineStep x dx θbar) (lineStep s ds θbar))
    (hθmin : ∀ θ : ℝ, InNinfMinus A b c β (lineStep x dx θ) (lineStep s ds θ) →
      LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θbar) (lineStep s ds θbar) ≤
        LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θ) (lineStep s ds θ)) :
    LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θbar) (lineStep s ds θbar) -
        LinearOptimization.interiorPointPotential (rho n β γ) x s ≤
      -(3 * (n : ℝ) ^ 2 * theta2Minus β γ x s dx ds / (β * γ) - n) *
        Real.log (1 / (1 - β)) := by sorry

end AdaptiveStepIPM.Potential

