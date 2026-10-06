import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- Theorem 1, p. 482. (A) There is a sequence of functions `g_n(x₂)` with `g_1 = L̃` such that
`C_n(x₁, w₁, x₂) = Ĉ_n(x₁, w₁) + g_n(x₂)` (16) for every `n ≥ 1` and every state with
`x₁ + w₁ ≤ x₂`. (B) It is optimal for installation 1 to use an optimal target `ŷ` of its isolated
problem (15), truncated at the stock available, `min(x₂, ŷ)`. -/
theorem theorem1_echelon_decomposition (M : Model) :
    (∃ g : ℕ → ℝ → ℝ, (∀ x₂ : ℝ, g 1 x₂ = M.Lt x₂) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ →
        M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + g n x₂) ∧
    (∀ (n : ℕ) (x₁ w₁ x₂ yiso : ℝ), x₁ + w₁ ≤ x₂ → x₁ + w₁ ≤ yiso →
      (∀ y : ℝ, x₁ + w₁ ≤ y → M.isoObj n x₁ w₁ yiso ≤ M.isoObj n x₁ w₁ y) →
      ∀ y z : ℝ, x₁ + w₁ ≤ y → y ≤ x₂ → 0 ≤ z →
        M.sysObj n x₁ w₁ x₂ (min x₂ yiso) z ≤ M.sysObj n x₁ w₁ x₂ y z) := by sorry

end ClarkScarf.Serial

