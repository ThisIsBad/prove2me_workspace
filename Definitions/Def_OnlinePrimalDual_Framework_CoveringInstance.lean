import Mathlib

namespace OnlinePrimalDual.Framework

/-- Buchbinder & Naor, *The Design of Competitive Online Algorithms via a Primal-Dual Approach*,
FnT TCS 2009, Section 4.1, p. 115-116 (PDF p. 26-27). The online packing-covering framework: a
primal covering LP `min ∑ᵢ cᵢxᵢ s.t. ∀j, ∑_{i ∈ S(j)} xᵢ ≥ 1, x ≥ 0` with `S : J → Finset I`
recording, for each covering constraint `j`, the set of primal variables it involves (the
book's simplified setting with `a(i,j) ∈ {0,1}`, `b(j) = 1`; Section 14 generalizes this).
`d` is the maximum constraint size `maxⱼ |S(j)|`, carried as an explicit hypothesis (`hd_bound`)
rather than derived, matching the book's own presentation (p. 118). Constraints/dual variables
are revealed one at a time in the order enumerated by `J`; the online algorithms of Section 4.2
only ever see, at the time constraint `j` is processed, the sets `S(j')` for `j' ≤ j` in that
order — this instance record itself is data available to the algorithm only progressively, which
is why the goal theorems below characterize the algorithm's *final* output via the invariants its
online update rule maintains, rather than by giving it the whole instance up front. -/
structure CoveringInstance (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] where
  /-- `S j` is the set of primal variables appearing in the `j`-th covering constraint. -/
  S : J → Finset I
  /-- The (positive) cost coefficients of the covering objective (Fig. 4.1's "non-negative", made
  strictly positive since every algorithm's update rule divides by `c i`). -/
  c : I → ℝ
  hc_pos : ∀ i, 0 < c i
  /-- `d = maxⱼ |S(j)|`, an explicit hypothesis-level bound, not a derived quantity. -/
  d : ℝ
  hd_pos : 0 < d
  hd_bound : ∀ j, (S j).card ≤ d

end OnlinePrimalDual.Framework
