import Mathlib

namespace TeschlODE.Shared

/-- Teschl, §11.4, p. 300 and §11.5, p. 303, (11.29): the shift map on the sequence space
`Σ_N = {0, …, N − 1}^{ℕ₀}` (11.27), `σ(x₀, x₁, …) = (x₁, x₂, …)`. Sequences are functions
`ℕ → Fin N`, indexed from `0`. -/
def shift {N : ℕ} (x : ℕ → Fin N) : ℕ → Fin N :=
  fun n => x (n + 1)

end TeschlODE.Shared
