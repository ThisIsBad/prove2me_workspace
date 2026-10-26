import Mathlib

open Matrix Filter Topology

namespace VanderbeiLP.CentralPath

/-- Theorem 17.1 (p. 261). Linear constraints `gᵢ(x) = (G x)ᵢ − βᵢ = 0`, `i = 1, …, m`; `f`
twice differentiable at `x*`. A critical point `x*` in the sense of (17.3) (feasible, and
`∇f(x*) = ∑ᵢ yᵢ ∇gᵢ(x*)` for some multipliers `y`) at which `ξᵀ H_f(x*) ξ < 0` (17.4) for every
`ξ ≠ 0` with `ξᵀ ∇gᵢ(x*) = 0` (17.5) is a local maximum of `f` on the feasible set. -/
theorem second_order_sufficient {m n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (G : Matrix (Fin m) (Fin n) ℝ) (β : Fin m → ℝ) (xstar : Fin n → ℝ) (y : Fin m → ℝ)
    (hf : ∀ᶠ x in 𝓝 xstar, DifferentiableAt ℝ f x)
    (hf2 : DifferentiableAt ℝ (fderiv ℝ f) xstar)
    (hfeas : G *ᵥ xstar = β)
    (hcrit : ∀ v : Fin n → ℝ, fderiv ℝ f xstar v = ∑ i, y i * (G i ⬝ᵥ v))
    (hhess : ∀ ξ : Fin n → ℝ, ξ ≠ 0 → (∀ i, ξ ⬝ᵥ G i = 0) →
      fderiv ℝ (fderiv ℝ f) xstar ξ ξ < 0) :
    IsLocalMaxOn f {x | G *ᵥ x = β} xstar := by sorry

end VanderbeiLP.CentralPath

