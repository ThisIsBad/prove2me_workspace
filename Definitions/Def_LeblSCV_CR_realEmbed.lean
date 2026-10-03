import Mathlib

namespace LeblSCV.CR

/-- The natural inclusion `ℝⁿ ⊂ ℂⁿ` (Lebl, pp. 104–105): `x ↦ (x₁ + 0i, …, xₙ + 0i)`. -/
def realEmbed {n : ℕ} (x : Fin n → ℝ) : Fin n → ℂ :=
  fun k => (x k : ℂ)

end LeblSCV.CR
