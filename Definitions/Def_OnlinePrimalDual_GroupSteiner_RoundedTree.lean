import Mathlib

namespace OnlinePrimalDual.GroupSteiner

/-- The rooted tree data the online group-Steiner rounding algorithm runs on (Buchbinder & Naor,
FnT TCS 2009, Section 11.2, p. 229): a finite edge type `E`, each edge's parent edge `parent e`
(the edge adjacent to `e` and closer to the root `r`, `e(p)` in the book's notation, `none`
exactly when `e` is incident to `r`), and a non-negative cost function. -/
structure RoundedTree (E : Type*) [Fintype E] [DecidableEq E] where
  /-- `parent e` is the edge adjacent to `e` and closer to the root (`e(p)`, p. 229); `none` iff
  `e` is incident to the root. -/
  parent : E → Option E
  /-- The non-negative edge cost `c : E → ℝ₊` (p. 224). -/
  cost : E → ℝ
  hcost_nonneg : ∀ e, 0 ≤ cost e

end OnlinePrimalDual.GroupSteiner
