import Mathlib
import Definitions.Def_RetailVariety_Fashion_Majorization

namespace RetailVariety.Fashion

/-- Lemma 2 (van Ryzin & Mahajan 1999, p. 1505; Hardy–Littlewood–Pólya / Karamata, quoted from
Marshall & Olkin 1979), for `g` convex on a convex set `s` containing every coordinate of `x` and
`y`; the paper's `g : ℝ → ℝ` convex is the case `s = univ`. -/
theorem lemma_2 {n : ℕ} {s : Set ℝ} {g : ℝ → ℝ} (hg : ConvexOn ℝ s g)
    (x y : Fin n → ℝ) (hxs : ∀ i, x i ∈ s) (hys : ∀ i, y i ∈ s) (hxy : Majorized x y) :
    ∑ i, g (x i) ≤ ∑ i, g (y i) := by sorry

end RetailVariety.Fashion

