import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_Hyperplanes

namespace KarpPapadimitriou.Generator

/-- Corollary after Lemma 4: the distance gap is constant on a flat disjoint from the new
hyperplane, including when the point on the flat is not rational. -/
theorem corollary_lemma_4 (n P m : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (H : Fin m → (Fin n → ℤ) × ℤ) (f : Fin n → ℤ) (g : ℤ)
    (r : EuclideanSpace ℝ (Fin n))
    (hsmall : ∀ i, SmallHyperplane P (H i).1 (H i).2)
    (hsmall_new : SmallHyperplane P f g)
    (hind : IndependentNormals H)
    (hr : r ∈ flat H)
    (hdisjoint : hyperplane f g ∩ flat H = ∅) :
    (1 : ℝ) / 2 ^ ((n + 1) * tParam n P c k) ≤ hyperplaneDistance f g r := by sorry

end KarpPapadimitriou.Generator

