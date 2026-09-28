import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi

namespace VapnikChervonenkis.GrowthFunction

/-- Vapnik and Chervonenkis (1971), p. 266, display after (1): `Φ(n, r) = Σ_{k=0}^{n} (r choose k)`
if `r > n`, and `Φ(n, r) = 2^r` if `r ≤ n`. (The printed summand reads `(r choose n)`, a misprint
for `(r choose k)`: with `(r choose n)` the formula already fails at `Φ(1, 2) = 3`.) -/
theorem phi_closed_form (n r : ℕ) :
    Shared.Phi n r = if n < r then ∑ k ∈ Finset.range (n + 1), r.choose k else 2 ^ r := by sorry

end VapnikChervonenkis.GrowthFunction
