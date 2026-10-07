import Mathlib

namespace TalagrandConc.OnePoint

open scoped ENNReal Classical

/-- Talagrand (1995), Eq. (2.1.1), p. 81: the Hamming distance from `x ∈ Ω^N` to a set `A ⊆ Ω^N`,
`f(A, x) = min { card {i ≤ N ; x_i ≠ y_i} ; y ∈ A }`.
It takes values in `ℝ≥0∞`; for `A = ∅` the infimum is `⊤ = +∞`. -/
noncomputable def hammingDistToSet {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : ℝ≥0∞ :=
  ⨅ y ∈ A, ((Finset.univ.filter (fun i => x i ≠ y i)).card : ℝ≥0∞)

/-- Talagrand (1995), Eq. (2.1.7), p. 84 (Remark 2.1.3): the weighted Hamming distance
`f(A, x) = inf { Σ { a_i : i ≤ N ; x_i ≠ y_i } : y ∈ A }` for weights `a : Fin N → ℝ`.
It takes values in `ℝ≥0∞`; for `A = ∅` the infimum is `⊤ = +∞`. -/
noncomputable def weightedHammingDistToSet {Ω : Type*} {N : ℕ} (a : Fin N → ℝ)
    (A : Set (Fin N → Ω)) (x : Fin N → Ω) : ℝ≥0∞ :=
  ⨅ y ∈ A, ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), ENNReal.ofReal (a i)

/-- Talagrand (1995), p. 82, Lemma 2.1.2: `a(t) = 1/2 + (e^t + e^{-t})/4`. -/
noncomputable def aOne (t : ℝ) : ℝ :=
  1 / 2 + (Real.exp t + Real.exp (-t)) / 4

/-- Talagrand (1995), Eq. (2.2.2), p. 85:
`a(α, t) = α^α / (α+1)^(α+1) · (e^t − e^{−t/α})^(1+α) / ((1 − e^{−t/α}) (e^t − 1)^α)`.
The formula is `0/0` at `t = 0`; there it is given its limit value `1` (the value of the
paper's variational form (2.2.3) at `t = 0`). Intended for `α > 0`, `t ≥ 0`. -/
noncomputable def aAlpha (α t : ℝ) : ℝ :=
  if t = 0 then 1 else
    α ^ α / (α + 1) ^ (α + 1) *
      ((Real.exp t - Real.exp (-t / α)) ^ (1 + α) /
        ((1 - Real.exp (-t / α)) * (Real.exp t - 1) ^ α))

/-- The exponential moment integrand `e^{t z}` for `t : ℝ` and an extended distance
`z : ℝ≥0∞`, computed in `EReal` (so `e^{t·∞} = ∞` for `t > 0` and `e^{0·∞} = 1`). -/
noncomputable def expMul (t : ℝ) (z : ℝ≥0∞) : ℝ≥0∞ :=
  EReal.exp ((t : EReal) * (z : EReal))

end TalagrandConc.OnePoint
