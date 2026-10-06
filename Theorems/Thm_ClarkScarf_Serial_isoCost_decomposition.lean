import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- Eqs. (6)–(7), p. 480: for `n ≥ 2` periods remaining the isolated installation-1 cost splits
as `Ĉ_n(x₁, w₁) = L(x₁) + α ∫₀^∞ L(x₁ + w₁ - t) φ(t) dt + f_n(x₁ + w₁)`. -/
theorem isoCost_decomposition (M : Model) (n : ℕ) (hn : 2 ≤ n) (x₁ w₁ : ℝ) :
    M.isoCost n x₁ w₁ =
      M.L x₁ + M.α * (∫ t in Ioi (0 : ℝ), M.L (x₁ + w₁ - t) * M.φ t) + M.fLag n (x₁ + w₁) := by sorry

end ClarkScarf.Serial

