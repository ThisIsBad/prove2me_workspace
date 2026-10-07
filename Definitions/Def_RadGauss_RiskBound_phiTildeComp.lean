import Mathlib

namespace RadGauss.RiskBound

/-- The class `φ̃ ∘ F = {(x, y) ↦ φ(y, f(x)) − φ(y, 0) : f ∈ F}` of Theorem 8 (p. 467), for a cost
function `φ : 𝒴 × 𝒜 → ℝ` (curried) and a class `F` of maps `𝒳 → 𝒜`; `0` is the distinguished
action `0 ∈ 𝒜`. Its members are functions on `𝒳 × 𝒴`. -/
def phiTildeComp {X Y A : Type*} [Zero A] (φ : Y → A → ℝ) (F : Set (X → A)) :
    Set (X × Y → ℝ) :=
  {h | ∃ f ∈ F, h = fun z => φ z.2 (f z.1) - φ z.2 0}

end RadGauss.RiskBound
