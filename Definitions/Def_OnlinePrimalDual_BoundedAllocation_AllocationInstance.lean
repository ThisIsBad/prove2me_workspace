import Mathlib

namespace OnlinePrimalDual.BoundedAllocation

/-- The bounded allocation instance data (Buchbinder & Naor, FnT TCS 2009, Section 13,
p. 237-238, Fig. 13.1): a finite set `I` of buyers with positive budgets `B`, a finite set `J`
of items revealed one at a time, each with a positive fixed price `b j` and a set `S j ⊆ I` of
interested buyers, subject to the per-item bound `|S(j)| ≤ d` on the number of interested
buyers, `d ≥ 2` (the chapter's standing assumption, p. 238: `d ≪ n`). -/
structure AllocationInstance (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] where
  /-- `S j` is the set of buyers interested in item `j`. -/
  S : J → Finset I
  /-- Buyer budgets, `B(i) > 0`. -/
  B : I → ℝ
  hB_pos : ∀ i, 0 < B i
  /-- Item prices, `b(j) > 0`. -/
  b : J → ℝ
  hb_pos : ∀ j, 0 < b j
  /-- The per-item bound on the number of interested buyers. -/
  d : ℕ
  hd : 2 ≤ d
  hSd : ∀ j, (S j).card ≤ d

end OnlinePrimalDual.BoundedAllocation
