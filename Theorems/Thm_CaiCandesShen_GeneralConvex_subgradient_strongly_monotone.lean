import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Basic

namespace CaiCandesShen.GeneralConvex

/-- Lemma 4.1, p. 1968: if `Z ∈ ∂f_τ(X)` and `Z' ∈ ∂f_τ(X')`, then
`⟨Z - Z', X - X'⟩ ≥ ‖X - X'‖_F²`. -/
theorem subgradient_strongly_monotone {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (X X' Z Z' : Mat n₁ n₂) (hZ : IsSubgradient (fτ τ) X Z) (hZ' : IsSubgradient (fτ τ) X' Z') :
    frobNorm (X - X') ^ 2 ≤ frobInner (Z - Z') (X - X') := by sorry

end CaiCandesShen.GeneralConvex
