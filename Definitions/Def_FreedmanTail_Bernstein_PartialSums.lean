import Mathlib

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Bernstein

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Freedman (1975), Definition (1.2)(f), p. 101: `S_n = X_1 + ⋯ + X_n`, so `S_0 = 0`.
The increments are indexed from `1`; `X 0` is never read. -/
def S (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, X i ω

/-- Freedman (1975), p. 101: `V_n = Var{X_n | ℱ_{n−1}}`, the conditional variance of the
`n`-th increment given `ℱ_{n−1}` (meaningful for `n ≥ 1`). -/
noncomputable def V (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ) : Ω → ℝ :=
  condVar (ℱ (n - 1)) (X n) P

/-- Freedman (1975), Definition (1.2)(g), p. 101: `T_n = V_1 + ⋯ + V_n`, so `T_0 = 0`. -/
noncomputable def T (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, V ℱ X P i ω

end FreedmanTail.Bernstein
