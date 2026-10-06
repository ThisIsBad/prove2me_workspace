import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- Theorem 2, p. 484: given critical numbers `x̄_{n+1}` of the isolated problem for every
`n + 1 ≥ 3` periods remaining, the functions `g_n` of (26), with `g_1 = L̃` and `Λ` of (25),
satisfy `C_n(x₁, w₁, x₂) = Ĉ_n(x₁, w₁) + g_n(x₂)` for every `n ≥ 1` and `x₁ + w₁ ≤ x₂`. -/
theorem theorem2_g_recursion (M : Model) (xbar : ℕ → ℝ)
    (hxbar : ∀ n : ℕ, 2 ≤ n → M.IsCriticalNumber n (xbar (n + 1))) :
    ∀ n : ℕ, 1 ≤ n → ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ →
      M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + M.gClark xbar n x₂ := by sorry

end ClarkScarf.Serial

