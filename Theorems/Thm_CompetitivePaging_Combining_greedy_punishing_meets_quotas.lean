import Mathlib

namespace CompetitivePaging.Combining

/-- Fiat et al. 1991, §6, proof of Theorem 6, p. 9, the scheduling claim. Index `A`'s units of
cost by `r = 0, 1, 2, …` (a lazy `A` pays one unit per fault). `pun r i` is `PUN(i, ·, σ)`, the
number of times `A` has punished `B(i)` by the time it has incurred cost `r`; it starts at `0`.
At its `(r+1)`-st unit of cost `A` punishes `choice r`, the `B(i)` for which
`c(i) · (PUN(i) + 1)` is least (ties broken arbitrarily); the chosen count grows by at least one,
and any count may also grow by incidental punishments. If every `c(i) > 0` and `∑ 1/c(i) ≤ 1`,
then for all positive integers `r` and all `i`, `B(i)` has been punished at least `⌊r / c(i)⌋`
times by the time `A` incurs cost `r`. -/
theorem greedy_punishing_meets_quotas {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    (hsum : ∑ i, 1 / c i ≤ 1) (choice : ℕ → Fin m) (pun : ℕ → Fin m → ℕ)
    (hpun0 : ∀ i, pun 0 i = 0)
    (hpun : ∀ (r : ℕ) (i : Fin m), pun r i + (if choice r = i then 1 else 0) ≤ pun (r + 1) i)
    (hgreedy : ∀ (r : ℕ) (j : Fin m),
      c (choice r) * ((pun r (choice r) : ℝ) + 1) ≤ c j * ((pun r j : ℝ) + 1)) :
    ∀ r : ℕ, 0 < r → ∀ i : Fin m, ⌊(r : ℝ) / c i⌋₊ ≤ pun r i := by sorry

end CompetitivePaging.Combining

