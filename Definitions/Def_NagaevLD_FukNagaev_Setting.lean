import Mathlib

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

/-- `S n X` is the sum `S_n = X₁ + ⋯ + X_n` (Nagaev 1979, §0, p. 745). The summands are indexed by
`Fin n`, i.e. `X 0, …, X (n-1)` stand for the paper's `X₁, …, X_n`. -/
def S {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, X i ω

/-- The truncated summand `X̃_i = X_i` if `X_i ≤ y_i`, `= 0` if `X_i > y_i` (proof of Theorem 1.3,
p. 749). -/
noncomputable def Xt {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) (i : Fin n)
    (ω : Ω) : ℝ :=
  if X i ω ≤ yv i then X i ω else 0

/-- The truncated sum `S̃_n = X̃₁ + ⋯ + X̃_n` (proof of Theorem 1.3, p. 749). -/
noncomputable def St {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) (ω : Ω) : ℝ :=
  ∑ i, Xt X yv i ω

/-- `μ(−∞, Y) = Σ ∫_{u ≤ y_i} u dF_i(u) = Σ E[X_i; X_i ≤ y_i]` (p. 748). -/
noncomputable def muY {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) : ℝ :=
  ∑ i, ∫ ω in {ω | X i ω ≤ yv i}, X i ω ∂P

/-- `B²(−∞, Y) = Σ ∫_{u ≤ y_i} u² dF_i(u) = Σ E[X_i²; X_i ≤ y_i]` (notation rule of pp. 747–748).
Every statement using it assumes `X_i²` is integrable on `{X_i ≤ y_i}` (the paper's finite
`B²(−∞, Y)`); otherwise Lean's Bochner integral would return `0` instead of `+∞`. -/
noncomputable def B2Y {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) : ℝ :=
  ∑ i, ∫ ω in {ω | X i ω ≤ yv i}, X i ω ^ 2 ∂P

/-- `A(t; 0, Y) = Σ ∫_{0 ≤ u ≤ y_i} |u|^t dF_i(u) = Σ E[|X_i|^t; 0 ≤ X_i ≤ y_i]` (notation rule of
pp. 747–748), with the real power `Real.rpow`. -/
noncomputable def AY {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∫ ω in {ω | 0 ≤ X i ω ∧ X i ω ≤ yv i}, |X i ω| ^ t ∂P

/-- `A_t⁺ = Σ ∫_{u ≥ 0} u^t dF_i(u) = Σ E[|X_i|^t; X_i ≥ 0]` (§0, p. 745). -/
noncomputable def Atplus {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (X : Fin n → Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∫ ω in {ω | 0 ≤ X i ω}, |X i ω| ^ t ∂P

/-- `B_n² = Σ σ_i²`, `σ_i² = Var X_i` (§0, p. 745). Mathlib's `variance` is `0` for a variable not
in `L²`; every statement using `Bn2` assumes `MemLp (X i) 2 P`. -/
noncomputable def Bn2 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (X : Fin n → Ω → ℝ) : ℝ :=
  ∑ i, variance (X i) P

/-- `P₄ = exp{β x/y − ((1 − α/2) x/y − μ/y) · log(β x y^{t−1}/A + 1)}` (p. 748), as a function of
the scalars `t, α, β, x, y`, `μ = μ(−∞, Y)` and `A = A(t; 0, Y)`. -/
noncomputable def P4 (t α β x y μ A : ℝ) : ℝ :=
  Real.exp (β * x / y - ((1 - α / 2) * x / y - μ / y) * Real.log (β * x * y ^ (t - 1) / A + 1))

/-- `P₅ = exp{(β − tα/2) x/y − (β x/y − μ/y) · log(β x y^{t−1}/A + 1)}` (p. 748). -/
noncomputable def P5 (t α β x y μ A : ℝ) : ℝ :=
  Real.exp ((β - t * α / 2) * x / y - (β * x / y - μ / y) * Real.log (β * x * y ^ (t - 1) / A + 1))

/-- `P₆ = exp{−αx(αx/2 − μ)/(e^t B)}` (p. 748), with `μ = μ(−∞, Y)` and
`B = B²(−∞, Y)`. At `B = 0` under the hypotheses of Theorem 1.3, also `μ = 0`, and the
paper's expression has limit `0`; use that value instead of Lean's division-by-zero value. -/
noncomputable def P6 (t α x μ B : ℝ) : ℝ :=
  if B = 0 then 0 else Real.exp (-(α * x * (α * x / 2 - μ) / (Real.exp t * B)))

/-- Condition (1.4) of Theorem 1.3 (p. 749):
`max[t, log(βxy^{t−1}/A + 1)] ≥ αxy/(e^t B)`, with `A = A(t; 0, Y)`, `B = B²(−∞, Y)`.
On the page `A = 0` makes the logarithm `+∞`, so (1.4) holds; this is the disjunct `A = 0`. -/
noncomputable def cond_1_4 (t α β x y B A : ℝ) : Prop :=
  A = 0 ∨ α * x * y / (Real.exp t * B) ≤ max t (Real.log (β * x * y ^ (t - 1) / A + 1))

/-- Condition (1.6) of Theorem 1.3 (p. 749):
`max[t, log(βxy^{t−1}/A + 1)] < αxy/(e^t B)`, which on the page forces `A = A(t; 0, Y)` finite
and nonzero; for `A ≥ 0` it is the exact complement of `cond_1_4`. -/
noncomputable def cond_1_6 (t α β x y B A : ℝ) : Prop :=
  0 < A ∧ max t (Real.log (β * x * y ^ (t - 1) / A + 1)) < α * x * y / (Real.exp t * B)

end NagaevLD.FukNagaev
