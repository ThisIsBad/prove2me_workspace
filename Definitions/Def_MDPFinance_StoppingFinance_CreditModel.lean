import Mathlib

open MeasureTheory
open scoped ENNReal

namespace MDPFinance.StoppingFinance

/-- The credit granting model of §11.2 (p. 340): `E = ℝ` (rating class), actions extend / cancel,
`Q^X` the Markov kernel of the information process, `c` the (measurable) one-stage reward of
extending, `g ≡ 0`, `β ∈ (0,1]`, and an **upper bounding function** `b` for the model (`c⁺ ≤ c_r b`,
`∫ b dQ^X(·|x) ≤ α_b b(x)`), which is what makes `(B_N)` hold and the value iteration finite. -/
structure CreditModel where
  QX : ℝ → Measure ℝ
  QX_prob : ∀ x, IsProbabilityMeasure (QX x)
  QX_meas : Measurable QX
  c : ℝ → ℝ
  c_meas : Measurable c
  beta : ℝ
  beta_mem : beta ∈ Set.Ioc (0 : ℝ) 1
  hbound : ∃ (b : ℝ → ℝ) (cr αb : ℝ), Measurable b ∧ (∀ x, 0 ≤ b x) ∧ 0 ≤ cr ∧
    (∀ x, max (c x) 0 ≤ cr * b x) ∧
    ∀ x, ∫⁻ y, ENNReal.ofReal (b y) ∂(QX x) ≤ ENNReal.ofReal (αb * b x)

/-- `J_0 ≡ 0`, `J_n(x) = max{0, c(x) + β ∫ J_{n−1}(y) Q^X(dy|x)}` (p. 340). -/
noncomputable def CreditModel.J (M : CreditModel) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | (n + 1) => fun x => max 0 (M.c x + M.beta * ∫ y, M.J n y ∂(M.QX x))

/-- `c̄_n(x) := c(x) + β ∫ J_{n−1} dQ^X(·|x)`, the value of extending with `n` periods left. -/
noncomputable def CreditModel.cbar (M : CreditModel) (n : ℕ) (x : ℝ) : ℝ :=
  M.c x + M.beta * ∫ y, M.J (n - 1) y ∂(M.QX x)

/-- The structural assumptions of p. 340: (i) `c` increasing, (ii) `Q^X` stochastically monotone
(`x ↦ ∫ v dQ^X(·|x)` increasing for every bounded increasing measurable `v`, Theorem B.3.3). -/
def CreditModel.StructuralAssumptions (M : CreditModel) : Prop :=
  Monotone M.c ∧
  ∀ v : ℝ → ℝ, Measurable v → Monotone v → (∃ C, ∀ y, |v y| ≤ C) →
    Monotone fun x => ∫ y, v y ∂(M.QX x)

/-- The Bayesian credit granting model (pp. 341-342): prior `μ₀` on the repayment probability,
not concentrated on `{0,1}` (so every posterior normaliser is positive), rewards `K₁ > 0` (pays)
and `K₀ < 0` (does not), `β ∈ (0,1]`. -/
structure BayesCreditModel where
  mu0 : Measure ℝ
  mu0_prob : IsProbabilityMeasure mu0
  mu0_supp : mu0 {p : ℝ | p < 0 ∨ 1 < p} = 0
  mu0_nondeg : 0 < mu0 (Set.Ioo (0 : ℝ) 1)
  K1 : ℝ
  K0 : ℝ
  K1_pos : 0 < K1
  K0_neg : K0 < 0
  beta : ℝ
  beta_mem : beta ∈ Set.Ioc (0 : ℝ) 1

/-- `q(s,n) = ∫ p^{s+1}(1−p)^{n−s} μ₀(dp) / ∫ p^s(1−p)^{n−s} μ₀(dp)`, `s ≤ n` (p. 341). -/
noncomputable def BayesCreditModel.q (M : BayesCreditModel) (s n : ℕ) : ℝ :=
  (∫ p, p ^ (s + 1) * (1 - p) ^ (n - s) ∂M.mu0) / ∫ p, p ^ s * (1 - p) ^ (n - s) ∂M.mu0

/-- (11.3): `c(s,n) = K₁q(s,n) + K₀(1 − q(s,n))`. -/
noncomputable def BayesCreditModel.c (M : BayesCreditModel) (s n : ℕ) : ℝ :=
  M.K1 * M.q s n + M.K0 * (1 - M.q s n)

/-- `J_0 ≡ 0`, `J_k(s,n) = max{0, c(s,n) + βq(s,n)J_{k−1}(s+1,n+1) + β(1−q(s,n))J_{k−1}(s,n+1)}`. -/
noncomputable def BayesCreditModel.J (M : BayesCreditModel) : ℕ → ℕ → ℕ → ℝ
  | 0 => fun _ _ => 0
  | (k + 1) => fun s n =>
      max 0 (M.c s n + M.beta * M.q s n * M.J k (s + 1) (n + 1)
              + M.beta * (1 - M.q s n) * M.J k s (n + 1))

/-- `c̄_k(s,n) := c(s,n) + βq(s,n)J_{k−1}(s+1,n+1) + β(1−q(s,n))J_{k−1}(s,n+1)` (p. 343). -/
noncomputable def BayesCreditModel.cbar (M : BayesCreditModel) (k s n : ℕ) : ℝ :=
  M.c s n + M.beta * M.q s n * M.J (k - 1) (s + 1) (n + 1)
    + M.beta * (1 - M.q s n) * M.J (k - 1) s (n + 1)

/-- The order on `E = {(s,n) | s ≤ n}` (p. 342): `(s,n) ≤ (s',n') :⟺ s ≤ s'` and
`n − s ≥ n' − s'`. -/
def BayesCreditModel.stateLe (p p' : ℕ × ℕ) : Prop :=
  p.1 ≤ p'.1 ∧ (p'.2 : ℤ) - (p'.1 : ℤ) ≤ (p.2 : ℤ) - (p.1 : ℤ)

end MDPFinance.StoppingFinance
