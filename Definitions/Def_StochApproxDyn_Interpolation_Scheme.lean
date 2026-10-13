import Mathlib

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- `τ_0 = 0` and `τ_n = Σ_{i=1}^n γ_i` (Benaïm 1999, §4.1, p. 12). The paper's step sizes are
`γ_1, γ_2, …`; the Lean sequence `γ : ℕ → ℝ` uses the same indices, and `γ 0` is never used. -/
def tau (γ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, γ (i + 1)

/-- The standing assumptions on the step sizes (p. 11): `γ_n ≥ 0` for `n ≥ 1`,
`Σ_k γ_k = ∞` (written: the partial sums `τ_n` tend to `+∞`) and `γ_n → 0`. -/
def IsStepSizeSeq (γ : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ γ (n + 1)) ∧ Tendsto (tau γ) atTop atTop ∧
    Tendsto (fun n => γ (n + 1)) atTop (𝓝 0)

/-- The recursion (7): `x_{n+1} − x_n = γ_{n+1} (F(x_n) + U_{n+1})` for all `n ∈ ℕ`
(`U 0` is never used). -/
def SatisfiesScheme {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → E)
    (γ : ℕ → ℝ) (x U : ℕ → E) : Prop :=
  ∀ n : ℕ, x (n + 1) - x n = γ (n + 1) • (F (x n) + U (n + 1))

/-- The "inverse" of `n ↦ τ_n`, `m(t) = sup{k ≥ 0 : t ≥ τ_k}` (8). When the standing assumptions
hold and `t ≥ 0`, the set is nonempty (it contains `0`) and bounded (`τ_k → ∞`), so `m(t)` is its
largest element; then `τ_{m(t)} ≤ t < τ_{m(t)+1}`, in particular `γ_{m(t)+1} > 0`. -/
noncomputable def mIdx (γ : ℕ → ℝ) (t : ℝ) : ℕ :=
  sSup {k : ℕ | tau γ k ≤ t}

/-- The affine interpolated process (p. 12): `X(τ_n + s) = x_n + s (x_{n+1} − x_n)/(τ_{n+1} − τ_n)`
for `0 ≤ s < γ_{n+1}`, written through `n = m(t)`, `s = t − τ_{m(t)}` and
`τ_{n+1} − τ_n = γ_{n+1}`. Only its values at `t ≥ 0` are used. -/
noncomputable def interpAffine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : ℕ → ℝ) (x : ℕ → E) (t : ℝ) : E :=
  x (mIdx γ t) + ((t - tau γ (mIdx γ t)) / γ (mIdx γ t + 1)) • (x (mIdx γ t + 1) - x (mIdx γ t))

/-- The piecewise constant interpolated process `X̄(τ_n + s) = x_n`, `0 ≤ s < γ_{n+1}` (p. 12). -/
noncomputable def interpConst {E : Type*} (γ : ℕ → ℝ) (x : ℕ → E) (t : ℝ) : E :=
  x (mIdx γ t)

/-- The piecewise constant noise process `Ū(τ_n + s) = U_{n+1}`, `0 ≤ s < γ_{n+1}` (p. 12). -/
noncomputable def noiseInterp {E : Type*} (γ : ℕ → ℝ) (U : ℕ → E) (t : ℝ) : E :=
  U (mIdx γ t + 1)

/-- The piecewise constant step-size process `γ̄(τ_n + s) = γ_{n+1}`, `0 ≤ s < γ_{n+1}` (p. 12). -/
noncomputable def stepInterp (γ : ℕ → ℝ) (t : ℝ) : ℝ :=
  γ (mIdx γ t + 1)

/-- `Δ(t, T) = sup_{0 ≤ h ≤ T} ‖∫_t^{t+h} Ū(s) ds‖` (10). Under the standing assumptions `Ū` takes
finitely many values on every bounded interval, so it is integrable there, `h ↦ ∫_t^{t+h} Ū` is
continuous, and the supremum (over a nonempty compact index set when `T ≥ 0`) is a genuine one. -/
noncomputable def Delta {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (γ : ℕ → ℝ) (U : ℕ → E) (t T : ℝ) : ℝ :=
  ⨆ h : Set.Icc (0 : ℝ) T, ‖∫ s in t..t + (h : ℝ), noiseInterp γ U s‖

/-- Assumption A1 for one horizon `T` (p. 12):
`lim_{n→∞} sup{‖Σ_{i=n}^{k−1} γ_{i+1} U_{i+1}‖ : k = n + 1, …, m(τ_n + T)} = 0`, written with `ε`.
An empty range of `k` imposes nothing. -/
def A1At {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (γ : ℕ → ℝ) (U : ℕ → E) (T : ℝ) :
    Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, n + 1 ≤ k → k ≤ mIdx γ (tau γ n + T) →
    ‖∑ i ∈ Finset.Ico n k, γ (i + 1) • U (i + 1)‖ ≤ ε

/-- Assumption A1 (p. 12): `A1At γ U T` for all `T > 0`. -/
def SatisfiesA1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (γ : ℕ → ℝ) (U : ℕ → E) :
    Prop :=
  ∀ T : ℝ, 0 < T → A1At γ U T

/-- Assumption A2 (p. 13): `sup_n ‖x_n‖ < ∞`. -/
def SatisfiesA2 {E : Type*} [NormedAddCommGroup E] (x : ℕ → E) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, ‖x n‖ ≤ B

/-- Assumption A2′ (p. 13): `F` is Lipschitz and bounded on a neighbourhood of `{x_n : n ≥ 0}`,
read as a *uniform* neighbourhood: for some `r > 0`, `F` is Lipschitz and bounded on the open
`r`-thickening of `{x_n : n ≥ 0}`. -/
def SatisfiesA2' {E : Type*} [NormedAddCommGroup E] (F : E → E) (x : ℕ → E) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ L : ℝ≥0, ∃ K : ℝ,
    LipschitzOnWith L F (Metric.thickening r (Set.range x)) ∧
      ∀ y ∈ Metric.thickening r (Set.range x), ‖F y‖ ≤ K

end StochApproxDyn.Interpolation
