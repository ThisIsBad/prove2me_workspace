import Mathlib
import Definitions.Def_FracPackCover_General_Basic

namespace FracPackCover.General

/-- Lemma 4.3 (pp. 26–27), with the explicit constant of its proof. Let `x ∈ P`, `λ = λ(x)`,
`α > 0`, `y` the dual solution of `x`, `Φ` its potential, and suppose `(x, λ)` and `y` violate (𝒢2)
where `x̃ ∈ P` attains `C_𝒢(y)`. If `0 ≤ σ ≤ λ/(24αρ²)` and `x̂ = (1 − σ)x + σx̃`, then
`Φ − Φ̂ ≥ ασλΦ/30` (the paper writes `Ω(ασλΦ)`). The error parameter `ε ∈ (0,1)` of the printed
statement is kept but unused. -/
theorem lemma_4_3 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (x : Fin n → ℝ) (hx : x ∈ P) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (α : ℝ) (hα : 0 < α)
    (xt : Fin n → ℝ) (hxt : xt ∈ P)
    (hmin : ∀ x' ∈ P, lagr A b (dualVec A b d α x) xt ≤ lagr A b (dualVec A b d α x) x')
    (hnG2 : ¬ G2 A b d x (lam A b d x) (dualVec A b d α x)
      (lagr A b (dualVec A b d α x) xt))
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ lam A b d x / (24 * α * ρ ^ 2)) :
    α * σ * lam A b d x * potential A b d α x / 30 ≤
      potential A b d α x - potential A b d α ((1 - σ) • x + σ • xt) := by sorry

end FracPackCover.General

