import Mathlib

namespace StochApproxDyn.WeakAPT

open scoped NNReal

/-- The block integrals of the proof of Theorem 10.1 (Benaïm 1999, §10, p. 61): for
`f : M → ℝ`, `T > 0` and `n ≥ 1`,
`U_n(f, T)(ω) = ∫_{(n-1)T}^{nT} f(X(s, ω)) ds`.
The paper's printed `f(X(x(s)))` is a typo for `f(X(s))`. The index follows the paper
(`n ≥ 1`); the value at `n = 0` is the empty integral `∫_0^0 = 0` and is never used. Time `s`
runs over `ℝ` for the interval integral and the path is evaluated at `s ∈ ℝ≥0`. -/
noncomputable def blockIntegral {Ω M : Type*} (X : ℝ≥0 → Ω → M) (f : M → ℝ) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∫ s in ((n - 1 : ℕ) : ℝ) * T..(n : ℝ) * T, f (X s.toNNReal ω)

end StochApproxDyn.WeakAPT
