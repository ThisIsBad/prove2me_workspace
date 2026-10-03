import Mathlib

namespace TeschlODE.Horseshoe

/-- Teschl, §11.5, p. 306 (after (11.35)) and §13.1, p. 333: the shift map on the two-sided
sequence space `Σ_N = {0, …, N − 1}^ℤ` (11.34), "defined as before": `σ(s)ₙ = sₙ₊₁` for all
`n ∈ ℤ`. On the two-sided space it is invertible. -/
def shiftZ {N : ℕ} (s : ℤ → Fin N) : ℤ → Fin N :=
  fun n => s (n + 1)

end TeschlODE.Horseshoe
