import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Corollary C.2.4, pp. 300–301. Assume `m_{iz} < ∞` for a distinguished state
`z` and all `i`. Let `r` be a finite nonnegative function on `S` and `H*` a finite set containing
`z` with (C.16): `∑_j P_{ij} r(j) < ∞` for `i ∈ H*` and `∑_j P_{ij}[r(j) − r(i)] ≤ −C(i)` for
`i ∉ H*` (written `∑_j P_{ij} r(j) + C(i) ≤ r(i)`). Then there is a finite nonnegative constant
`F` with `c_{iz} ≤ r(i) + F m_{iz}` for `i ≠ z`; if `H* = {z}`, then `c_{iz} ≤ r(i)` for `i ≠ z`;
finally `c_{zz} < ∞`. -/
theorem lyapunov_return_cost_finite {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0) (z : S)
    (hm : ∀ i, meanPassage M {z} i < ⊤) (r : S → ℝ≥0) (Hs : Finset S) (hzH : z ∈ Hs)
    (hH : ∀ i ∈ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) < ⊤)
    (hdrift : ∀ i ∉ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) + C i ≤ r i) :
    (∃ F : ℝ≥0, ∀ i, i ≠ z → passageCost M C {z} i ≤ r i + F * meanPassage M {z} i) ∧
    (Hs = {z} → ∀ i, i ≠ z → passageCost M C {z} i ≤ r i) ∧
    passageCost M C {z} z < ⊤ := by sorry

end SennottDP.MarkovCost
