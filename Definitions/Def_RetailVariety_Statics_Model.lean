import Mathlib
import Definitions.Def_RetailVariety_Structure_Model

open MeasureTheory ProbabilityTheory

namespace RetailVariety.Statics

/-- The prefix assortment `A_i = {1, …, i}` of the paper (§3.1, p. 1503), 0-based: the variants
`j : Fin n` with `j.val < i`. So `A n 0 = ∅` and `A n n = Finset.univ`. It is the same set as
`RetailVariety.Structure.popularSet n i`, under the name the comparative statics use. -/
def A (n i : ℕ) : Finset (Fin n) :=
  RetailVariety.Structure.popularSet n i

/-- The standard normal c.d.f. `Φ`. -/
noncomputable def stdNormalCdf (x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) x

/-- The critical fractile (6), p. 1502: `z = Φ⁻¹(1 - c/p)`, the least `x` with
`Φ(x) ≥ 1 - c/p`. This is `RetailVariety.Structure.criticalFractile`, the `z` inside the profit
`RetailVariety.Structure.profitI`. For `0 < c < p` it is the unique `x` with `Φ(x) = 1 - c/p`. -/
noncomputable def criticalFractile (p c : ℝ) : ℝ :=
  RetailVariety.Structure.criticalFractile p c

end RetailVariety.Statics
