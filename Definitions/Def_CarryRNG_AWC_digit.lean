import Mathlib

namespace CarryRNG.AWC

/-- The `j`-th base-`b` digit after the point in the expansion of `k/m` (Section 4.1, p. 467),
for `j ≥ 1`: `⌊b · ((b^(j-1) k) mod m) / m⌋`. The value at `j = 0` equals the value at `j = 1`
and is never used. -/
def digit (b m k j : ℕ) : ℕ := b * (b ^ (j - 1) * k % m) / m

end CarryRNG.AWC
