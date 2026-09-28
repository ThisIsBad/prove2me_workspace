import Mathlib

namespace OnlinePrimalDual.Caching

/-- Buchbinder & Naor, *The Design of Competitive Online Algorithms via a Primal-Dual Approach*,
FnT TCS 2009, Section 7.1.1, p. 150-152 (PDF p. 61-63). The weighted-caching LP's eviction-charged
formulation: `V` indexes primal variables `x(p,j)` (page `p`'s `j`-th eviction interval); `Time`
indexes the online constraints, one per request time `t`. `S t` is the set of variables appearing
in the constraint at time `t` (the book's `B(t) \ {pₜ}`, restricted to each page's currently-active
interval variable `x(p, r(p,t))`); `rhs t` is the constraint's right-hand side `|B(t)| − k`
(possibly non-positive, in which case the constraint at `t` is vacuous). `c v` is the fetching cost
of the page underlying variable `v`, required `≥ 1` exactly as the book's own standing assumption
`cp ≥ 1` (p. 150); `k` is the cache size. Unlike Chapter 4's framework (`b(j) = 1` throughout),
this LP's right-hand side varies with `t`, which is why `rhs` is carried explicitly rather than
fixed at `1`. -/
structure CachingInstance (V Time : Type*) [Fintype V] [Fintype Time] [DecidableEq V] where
  /-- `S t` is the set of eviction variables `x(p, r(p,t))` appearing in the primal constraint
  revealed at time `t` (the book's `B(t) \ {pₜ}`, p. 151). -/
  S : Time → Finset V
  /-- The constraint's right-hand side at time `t`, `|B(t)| − k` (p. 151); may be non-positive,
  in which case the constraint at `t` holds vacuously. -/
  rhs : Time → ℝ
  /-- The fetching cost of the page underlying variable `v`. -/
  c : V → ℝ
  /-- The book's own standing assumption for weighted caching: `cp ≥ 1` (p. 150). -/
  hc_pos : ∀ v, 1 ≤ c v
  /-- The cache size. -/
  k : ℕ
  hk_pos : 0 < k

end OnlinePrimalDual.Caching
