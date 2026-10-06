import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model
import Definitions.Def_BinPacking_FirstFit_W

namespace BinPacking.FirstFit

/-- Claim 2.2.4 (p. 306), with alternative (i) read as `b₁ ≤ 1/2` (the printed `b₁ < 1/2` is a
misprint: FF on `(0.6, 0.5)` is a counterexample): in the completed FF packing (resp. BF
packing) of `L`, if bin `j` has coarseness `α < 1/2` and its `W`-weights sum to `1 − β` with
`β > 0`, then either the bin holds a single item `b₁ ≤ 1/2`, or its level is at most
`1 − α − (5/9)β`. -/
theorem weight_deficit_bound (L : List ℝ) (hL : IsList L) :
    (∀ (j : ℕ) (hj : j < (ffPack L).length) (β : ℝ), coarseness (ffPack L) j < 1 / 2 →
        0 < β → (((ffPack L)[j]).map W).sum = 1 - β →
        (∃ b : ℝ, (ffPack L)[j] = [b] ∧ b ≤ 1 / 2) ∨
          ((ffPack L)[j]).sum ≤ 1 - coarseness (ffPack L) j - 5 / 9 * β) ∧
    (∀ (j : ℕ) (hj : j < (bfPack L).length) (β : ℝ), coarseness (bfPack L) j < 1 / 2 →
        0 < β → (((bfPack L)[j]).map W).sum = 1 - β →
        (∃ b : ℝ, (bfPack L)[j] = [b] ∧ b ≤ 1 / 2) ∨
          ((bfPack L)[j]).sum ≤ 1 - coarseness (bfPack L) j - 5 / 9 * β) := by sorry

end BinPacking.FirstFit

