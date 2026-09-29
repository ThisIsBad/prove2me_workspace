import Mathlib

namespace BassokSubstitution

/-- The economic data of the single-period `N`-product model with full downward substitution
(Bassok–Anupindi–Akella 1999, §2.1). Products and demand classes are both indexed by `Fin N`;
the paper's product/class `k` (1-based) is index `k - 1` here, so product `0` is the most
flexible product. Demand of class `i` may be served by product `j` only when `j ≤ i`.

* `c j` — unit purchase cost of product `j`;
* `p i` — unit revenue of a satisfied unit of class `i` (independent of the product used);
* `penalty i` — unit backorder (shortage) cost `π_i` of class `i`;
* `s j` — effective unit salvage value `s̄_j - h̄_j` of a leftover unit of product `j`
  (may be negative);
* `b` — unit substitution cost. -/
structure Model (N : ℕ) where
  c : Fin N → ℝ
  p : Fin N → ℝ
  penalty : Fin N → ℝ
  s : Fin N → ℝ
  b : ℝ

variable {N : ℕ}

/-- Net revenue `a_{j i}` of using one unit of product `j` for one unit of demand class `i`
(meaningful for `j ≤ i`): `p_i` if `j = i`, and `p_i - b` if `j < i`. -/
def Model.netRevenue (M : Model N) (j i : Fin N) : ℝ :=
  if j = i then M.p i else M.p i - M.b

/-- `T_k = p_k + π_k - b`. -/
def Model.T (M : Model N) (k : Fin N) : ℝ :=
  M.p k + M.penalty k - M.b

/-- Assumption 1: `π_i + p_i ≥ π_j + p_j` for `i < j`. -/
def Model.Assumption1 (M : Model N) : Prop :=
  ∀ i j : Fin N, i < j → M.penalty j + M.p j ≤ M.penalty i + M.p i

/-- Assumption 2: `s_i ≥ s_j` for `i < j`. -/
def Model.Assumption2 (M : Model N) : Prop :=
  ∀ i j : Fin N, i < j → M.s j ≤ M.s i

/-- Assumption 3: `a_{ij} + π_j - s_i ≥ 0` for `i ≤ j` (product `i`, class `j`). -/
def Model.Assumption3 (M : Model N) : Prop :=
  ∀ i j : Fin N, i ≤ j → 0 ≤ M.netRevenue i j + M.penalty j - M.s i

end BassokSubstitution
