import Mathlib

namespace AccelScal.UCMonopoly

/-- Technology parameters of the R&D project, (2): `u(R) = A R^β`, `λ(R) = η R^γ`. -/
structure Tech where
  A : ℝ
  β : ℝ
  η : ℝ
  γ : ℝ

namespace Tech

/-- Standing assumptions: (2) (`A > 0`, `η > 0`, `β, γ ∈ [0,1)`, `β + γ < 1`) and the disclosed
condition `A η > 1` (investment takes place: the project value at `R̲ = 1` is positive). -/
def Standing (T : Tech) : Prop :=
  0 < T.A ∧ 0 < T.η ∧ 0 ≤ T.β ∧ T.β < 1 ∧ 0 ≤ T.γ ∧ T.γ < 1 ∧ T.β + T.γ < 1 ∧ 1 < T.A * T.η

/-- Expected project payoff `u(R) = A R^β`, (2). -/
noncomputable def u (T : Tech) (R : ℝ) : ℝ := T.A * R ^ T.β

/-- Discovery intensity `λ(R) = η R^γ`, (2). -/
noncomputable def lam (T : Tech) (R : ℝ) : ℝ := T.η * R ^ T.γ

/-- Upper end of the investment range, (7): `R̄ = (A η)^{1/(1-(β+γ))}`. -/
noncomputable def Rbar (T : Tech) : ℝ := (T.A * T.η) ^ (1 / (1 - (T.β + T.γ)))

end Tech

/-- The R&D part of the unconstrained monopoly's objective (4) at intensity `R` and discount
rate `r`: the discovery time `τ_d` is exponential with rate `λ(R)`; the firm pays `R` per unit
time on `[0, τ_d]` and receives the expected payoff `u(R)` at `τ_d`, everything discounted at
rate `r`. -/
noncomputable def ucPayoff (T : Tech) (r R : ℝ) : ℝ :=
  ∫ τ, (Real.exp (-r * τ) * T.u R - R * ∫ t in (0 : ℝ)..τ, Real.exp (-r * t))
    ∂(ProbabilityTheory.expMeasure (T.lam R))

/-- `R*_uc`: the set of maximizers of `ucPayoff T r` over the range `[R̲, R̄] = [1, R̄]` of (7). -/
noncomputable def RstarUC (T : Tech) (r : ℝ) : Set ℝ :=
  {R | R ∈ Set.Icc 1 T.Rbar ∧ ∀ R' ∈ Set.Icc 1 T.Rbar, ucPayoff T r R' ≤ ucPayoff T r R}

/-- The paper's `ln V(R) = ln(uλ - R) - ln(λ + r)` of (A.1), the logarithm of the closed form
(5) of the project value. -/
noncomputable def logV (T : Tech) (r R : ℝ) : ℝ :=
  Real.log (T.u R * T.lam R - R) - Real.log (T.lam R + r)

/-- `OrderedAbove S S'`: every element `x` of `S` lies weakly below every element `y` of `S'`,
and strictly below it whenever `x > R̲ = 1`. This is how "`∂R*/∂s > 0`" is posed for optimal
sets. -/
def OrderedAbove (S S' : Set ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S', x ≤ y ∧ (1 < x → x < y)

end AccelScal.UCMonopoly
