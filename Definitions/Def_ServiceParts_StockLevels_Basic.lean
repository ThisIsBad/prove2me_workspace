import Mathlib
import Definitions.Def_ServiceParts_Palm_CompoundResupplySystem

namespace ServiceParts.StockLevels

/-- First forward difference of a function on the stock levels `s = 0, 1, …`:
`Δf(s) = f(s + 1) - f(s)` (Muckstadt 2005, p. 53). -/
def fdiff (f : ℕ → ℝ) (s : ℕ) : ℝ := f (s + 1) - f s

/-- Second forward difference `Δ²f(s) = Δf(s + 1) - Δf(s)` (Muckstadt 2005, p. 53). -/
def fdiff2 (f : ℕ → ℝ) (s : ℕ) : ℝ := fdiff f (s + 1) - fdiff f s

/-- The Poisson probability `e^{-a} a^x / x!` of the value `x` for mean `a`
(Muckstadt 2005, p. 52: `p(x|λτ̄)` for simple Poisson demand, with `a = λτ̄`). -/
noncomputable def poissonPmf (a : ℝ) (x : ℕ) : ℝ :=
  Real.exp (-a) * a ^ x / (x.factorial : ℝ)

/-- The fill rate under simple Poisson demand, `F(s) = Σ_{x < s} p(x|a)`
(Muckstadt 2005, p. 52), for stock level `s` and mean lead-time demand `a = λτ̄`. -/
noncomputable def poissonFillRate (a : ℝ) (s : ℕ) : ℝ :=
  ∑ x ∈ Finset.range s, poissonPmf a x

end ServiceParts.StockLevels
