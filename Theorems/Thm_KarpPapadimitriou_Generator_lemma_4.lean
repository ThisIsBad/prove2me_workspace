import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_Hyperplanes

namespace KarpPapadimitriou.Generator

/-- Lemma 4: a rational point outside a small hyperplane has a quantified distance gap. -/
theorem lemma_4 (n P : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (r : Fin n → ℚ) (f : Fin n → ℤ) (g : ℤ)
    (hsmall : SmallHyperplane P f g)
    (hden : ∀ i, (r i).den ≤ 2 ^ tParam n P c k)
    (hout : dotQ f r ≠ (g : ℚ)) :
    (1 : ℝ) / 2 ^ ((n + 1) * tParam n P c k) ≤
      hyperplaneDistance f g (realPoint r) := by sorry

end KarpPapadimitriou.Generator

