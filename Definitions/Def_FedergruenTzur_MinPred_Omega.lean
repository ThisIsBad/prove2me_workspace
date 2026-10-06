import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Model

/-!
# Federgruen–Tzur (1991), §2: potential costs and the Minimal Optimal Predecessors list `Ω(j)`

A. Federgruen and M. Tzur, Management Science 37(8), 1991, §2, pp. 914–915.

At iteration `j` the future demands `d_{j+1}, d_{j+2}, …` are unknown parameters, so the cumulative
demand of a horizon `t ≥ j` is a *potential* value `x ≥ D(j)`.

* `potCost j l x = F(l-1) + K_l + S(l, j) + c_l (x - D(l-1)) + (x - D(j)) (H(j-1) - H(l-1))` is the
  cost (2) of a last setup in `l ≤ j` for a horizon `t ≥ j` with `D(t) = x`, minus the carrying cost
  `S(j, t)` of the post-`j` demand from period `j` on, which is the same for every `l ≤ j`
  (so `F(l, t) = potCost j l (D t) + S(j, t)`; this is (2) rewritten with (1a)).
* `IsLowestOptimal j l x`: `l` is the lowest index `i ∈ {1, …, j}` minimizing `potCost j i x`.
* `Omega j`: the periods `1 ≤ l ≤ j` for which there are reals `a < b` with `D(j) ≤ a` such that `l`
  is the lowest-index optimum for every potential cumulative demand `x ∈ (a, b)`.

**Formalization Note (open-interval reading of `Ω(j)`).** The page defines `Ω(j)` with a single
potential cumulative demand `D ≥ D(j)` at which `l` is the lowest index with
`F(l, t) = min_{1 ≤ i ≤ j} F(i, t)`. With that literal reading Theorem 1(a) ("⇒") and (c) fail
whenever two lines tie exactly at a breakpoint. The definition here requires `l` to be the lowest
optimal index on a nondegenerate open interval of potential cumulative demands above `D(j)`, which is
the paper's own description of the list on p. 915: "the `k`th element of the list is the unique
optimal last setup period for any horizon `t ≥ j` with potential cumulative demand
`g(k) < D < g(k + 1)`".
-/

namespace FedergruenTzur.MinPred

namespace LotSizing

variable (P : LotSizing)

/-- Cost of a last setup in period `l ≤ j` at potential cumulative demand `x` for a horizon beyond
`j`, without the `l`-independent term `S(j, t)`. -/
noncomputable def potCost (j l : ℕ) (x : ℝ) : ℝ :=
  P.Fopt (l - 1) + P.K l + P.S l j + P.c l * (x - P.D (l - 1))
    + (x - P.D j) * (P.H (j - 1) - P.H (l - 1))

/-- `l` is the lowest index in `{1, …, j}` attaining `min_{1 ≤ i ≤ j} potCost j i x`. -/
def IsLowestOptimal (j l : ℕ) (x : ℝ) : Prop :=
  (∀ i ∈ Finset.Icc 1 j, P.potCost j l x ≤ P.potCost j i x) ∧
    (∀ i ∈ Finset.Icc 1 j, i < l → P.potCost j l x < P.potCost j i x)

/-- The `j`th Minimal Optimal Predecessors list `Ω(j)` (open-interval reading). -/
noncomputable def Omega (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 j).filter fun l =>
    ∃ a b : ℝ, P.D j ≤ a ∧ a < b ∧ ∀ x ∈ Set.Ioo a b, P.IsLowestOptimal j l x

end LotSizing

end FedergruenTzur.MinPred
