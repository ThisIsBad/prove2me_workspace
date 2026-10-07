import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_EquilibriumProcess

namespace SmithRegenerative.CLT

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The counting variable `n_t` of (2·1·3) (p. 9): "the greatest integer `k` such that
`T_{k−1} ≤ t`". For `t ≥ 0`, since `T₋₁ = 0 ≤ t` and the epochs are non-decreasing, this is the
number of indices `j ≥ 0` with `T_j ≤ t`, i.e. the number of regenerations in `[0, t]`
(with `t₀ = 0`, `n_t ≥ 1`).

**Formalization Note** `Nat.card` of an infinite type is `0`, so on the event where infinitely many
epochs are `≤ t` (a null event when the cycle lengths are not zero with probability one) the value
is `0`; finiteness is never assumed. For `t < 0` the value is `0` as well; only `t → ∞` matters. -/
noncomputable def count (τ : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  Nat.card {j : ℕ // SmithRegenerative.Equilibrium.epoch τ j ω ≤ t}

/-- The overshoot `Z_t = Σ_{i=1}^{n_t+1} t_i − t` (p. 26). With `t₀ = 0` the sum is the SmithRegenerative.Equilibrium.epoch
`T_{n_t+1}`, so `t + Z_t = T_{n_t+1}`. -/
noncomputable def overshoot (τ : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  SmithRegenerative.Equilibrium.epoch τ (count τ t ω + 1) ω - t

/-- The cycle increment `y_n = Δ_n w_t = w_{T_n} − w_{T_{n−1}}` (§5·1, p. 23) of a real process
`w : ℝ → Ω → ℝ` (time first). Only `n ≥ 1` is used; at `n = 0` the value is `0`
(Lean's `0 − 1 = 0`). -/
def incr (w : ℝ → Ω → ℝ) (τ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  w (SmithRegenerative.Equilibrium.epoch τ n ω) ω - w (SmithRegenerative.Equilibrium.epoch τ (n - 1) ω) ω

/-- The variation process `w̃_t = ∫₀^t |dw_t|` (5·1·1), p. 23: the total variation of the path
`s ↦ w_s(ω)` on `[0, t]`. As the paper allows ("on the set of zero probability for which this
definition breaks down we may take `w̃_t = 0` for all `t`"), it is `0` for all `t` on the paths
that have infinite variation on some `[0, s]`. -/
noncomputable def variationProc (w : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ := by
  classical
  exact if ∀ s : ℝ, eVariationOn (fun u => w u ω) (Set.Icc 0 s) ≠ ⊤ then
    (eVariationOn (fun u => w u ω) (Set.Icc 0 t)).toReal
  else 0

/-- The variation increment `ỹ_n = Δ_n w̃_t = w̃_{T_n} − w̃_{T_{n−1}}` (p. 23). -/
noncomputable def varIncr (w : ℝ → Ω → ℝ) (τ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  variationProc w (SmithRegenerative.Equilibrium.epoch τ n ω) ω - variationProc w (SmithRegenerative.Equilibrium.epoch τ (n - 1) ω) ω

/-- A **renewal process with `t₀ = 0`** (§2·1, p. 9, and the standing assumption of p. 27):
`t₁, t₂, …` are independent, non-negative, identically distributed random variables "which are
not zero with probability one", i.e. `P{t₁ = 0} < 1`; and `t₀ = 0`. -/
structure IsRenewal (P : Measure Ω) (τ : ℕ → Ω → ℝ) : Prop where
  measurable : ∀ n, Measurable (τ n)
  nonneg : ∀ n ω, 0 ≤ τ n ω
  delay_zero : ∀ ω, τ 0 ω = 0
  indep : iIndepFun (fun n => τ (n + 1)) P
  ident : ∀ n, IdentDistrib (τ (n + 1)) (τ 1) P P
  not_ae_zero : P {ω | τ 1 ω = 0} < 1

/-- `μ₁ = E t_i` (2·1·1). Meaningful under `Integrable (τ 1) P` (`μ₁ < ∞`), which every statement
that uses it assumes. -/
noncomputable def mu1 (P : Measure Ω) (τ : ℕ → Ω → ℝ) : ℝ := ∫ ω, τ 1 ω ∂P

/-- The cycle vector of `M` processes in cycle `n`: `(t_n, (y_n^{(i)})_i, (ỹ_n^{(i)})_i)`. -/
noncomputable def cycleVec {M : ℕ} (w : Fin M → ℝ → Ω → ℝ) (τ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ℝ × (Fin M → ℝ) × (Fin M → ℝ) :=
  (τ n ω, fun i => incr (w i) τ n ω, fun i => varIncr (w i) τ n ω)

/-- **`M` cumulative processes based on the same sequence of regeneration points** (§5·1,
pp. 22–23, and Theorem 10, p. 30). `τ` is a renewal process with `t₀ = 0`, and each
`w^{(i)} : ℝ → Ω → ℝ` is a real process (a random variable at each time) with

* `w₀^{(i)} = 0` (standing assumption, p. 27: "we shall assume that `t₀ = 0` and `w₀ = 0`");
* (C2) with probability one, `w^{(i)}` is of bounded variation on every finite interval `[0, s]`;
* (C1), read jointly: the cycle vectors `(t_n, y_n^{(1)}, …, y_n^{(M)}, ỹ_n^{(1)}, …, ỹ_n^{(M)})`,
  `n = 1, 2, …`, are independent and identically distributed.

**Formalization Note** The paper's (C1) asks that the increments `w_{T_n} − w_{T_{n−1}}` be
i.i.d. and remarks that `w̃` then satisfies (C1) too; Theorem 10 ("based on the same sequence of
regeneration points"), its covariance matrices, and the derivation of Corollary 9·1 from
Theorem 9 all use that the whole cycle vectors are i.i.d., which is how (C1) is read here. No
independence between the components of a cycle vector is assumed. `M = 1` is the single cumulative
process of Theorem 9 and Corollary 9·1. -/
structure IsCumulativeModel {M : ℕ} (P : Measure Ω) (τ : ℕ → Ω → ℝ)
    (w : Fin M → ℝ → Ω → ℝ) : Prop where
  renewal : IsRenewal P τ
  measurable : ∀ i s, Measurable (w i s)
  start_zero : ∀ i ω, w i 0 ω = 0
  boundedVariation : ∀ i, ∀ᵐ ω ∂P, ∀ s : ℝ, eVariationOn (fun u => w i u ω) (Set.Icc 0 s) ≠ ⊤
  indep : iIndepFun (fun n => cycleVec w τ (n + 1)) P
  ident : ∀ n, IdentDistrib (cycleVec w τ (n + 1)) (cycleVec w τ 1) P P

/-- The covariance matrix `a_kl = cov(X^{(k)}, X^{(l)})` of a family of real random variables. -/
noncomputable def covMatrix {M : ℕ} (P : Measure Ω) (X : Fin M → Ω → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun k l => covariance (X k) (X l) P

end SmithRegenerative.CLT
