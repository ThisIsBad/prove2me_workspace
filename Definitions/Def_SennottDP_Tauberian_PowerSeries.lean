import Mathlib

open scoped ENNReal NNReal

namespace SennottDP.Tauberian

/-- Sennott (1999), §A.3, p. 279, (A.20): the power series with nonnegative terms
`U(α) = ∑_{n=0}^∞ α^n u_n`, for `α ∈ [0, ∞)` and a sequence `u_n ∈ [0, ∞]`.
The sum is taken in `[0, ∞]`, so it always exists (it may be `∞`). At `α = 0` the
convention `0^0 = 1` gives `U(0) = u_0`. -/
noncomputable def U (u : ℕ → ℝ≥0∞) (α : ℝ≥0) : ℝ≥0∞ :=
  ∑' n, (α : ℝ≥0∞) ^ n * u n

/-- Sennott (1999), §A.3, p. 279, (A.21): the radius of convergence
`R = (lim sup_{n→∞} u_n^{1/n})^{-1} ∈ [0, ∞]`, with `0⁻¹ = ∞` and `∞⁻¹ = 0`.
(The value of `u_0^{1/0}` is irrelevant to the `lim sup`.) -/
noncomputable def radius (u : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  (Filter.limsup (fun n : ℕ => u n ^ ((n : ℝ)⁻¹)) Filter.atTop)⁻¹

/-- Sennott (1999), p. 282, Theorem A.4.2: the partial sums `w_n = ∑_{k=0}^{n-1} u_k`
(the book uses `n ≥ 1`; `w 0 = 0` is the empty sum). -/
noncomputable def w (u : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range n, u k

/-- The Cesàro mean `w_n / n ∈ [0, ∞]` of Theorem A.4.2. Its value at `n = 0` (`0 / 0 = 0`
in `ℝ≥0∞`) plays no role: it is only used through limits as `n → ∞`. -/
noncomputable def cesaroMean (u : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  w u n / n

/-- The Abel mean `(1 - α) U(α) ∈ [0, ∞]` of Theorem A.4.2, used for `α ∈ [0, 1)`
(where `1 - α > 0`, so `(1 - α) · ∞ = ∞`); only its behaviour as `α → 1⁻` matters. -/
noncomputable def abelMean (u : ℕ → ℝ≥0∞) (α : ℝ≥0) : ℝ≥0∞ :=
  (1 - (α : ℝ≥0∞)) * U u α

end SennottDP.Tauberian
