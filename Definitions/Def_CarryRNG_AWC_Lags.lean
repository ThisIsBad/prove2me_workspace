import Mathlib

namespace CarryRNG.AWC

/-- The two lags `r` and `s` of an add-with-carry generator, with the paper's standing
convention `0 < s < r` (Section 2, p. 465; Section 3, p. 466). -/
structure Lags where
  r : ℕ
  s : ℕ
  hs : 0 < s
  hsr : s < r

end CarryRNG.AWC
