import Mathlib

namespace MechanismDesign.Correlated

open MeasureTheory

namespace Indep

/-!
Bayesian mechanism design with independent types (Börgers, *An Introduction to the Theory of
Mechanism Design*, §6.2–6.3, pp.114–118).

Agents form a finite set `ι`; agent `i`'s type set `Θ i` is an abstract measurable space, and the
alternatives form a measurable space `A`. Agent `i`'s utility from alternative `a` and transfer `t`
is `u i a θᵢ - t`. Types are independent (Definition 6.1): the common prior is the product
`Measure.pi ρ` of probability measures `ρ i` on the `Θ i`, so that the conditional distribution of
`θ₋ᵢ` given `θᵢ` is the same for every `θᵢ`. An integral over `Θ₋ᵢ` against that conditional
distribution of a function of `(y, θ₋ᵢ)` is written as the integral over the whole prior of the
function evaluated at `Function.update θ i y` (which does not depend on `θ i`).
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*} [∀ i, MeasurableSpace (Θ i)]
  {A : Type*} [MeasurableSpace A]

/-- The common prior with independent types: the product of the type distributions `ρ i`. -/
noncomputable def prior (ρ : ∀ i, Measure (Θ i)) : Measure (∀ i, Θ i) :=
  Measure.pi ρ

/-- A direct mechanism (Definition 6.2, p.115): a decision rule `q : Θ → A` and a payment rule
`t i : Θ → ℝ` for every agent `i`. -/
structure DirectMechanism (ι : Type*) (Θ : ι → Type*) (A : Type*) where
  /-- the decision rule `q` -/
  q : (∀ i, Θ i) → A
  /-- the payment rule `t i` of agent `i` -/
  t : ι → (∀ i, Θ i) → ℝ

/-- The interim decision rule `Qᵢ(y)` (6.1), p.116: the distribution on `A` of the decision
`q(y, θ₋ᵢ)` when agent `i` reports `y` and the other types are drawn from the prior. -/
noncomputable def interimDist (ρ : ∀ i, Measure (Θ i)) (q : (∀ i, Θ i) → A) (i : ι) (y : Θ i) :
    Measure A :=
  (prior ρ).map fun θ => q (Function.update θ i y)

/-- The interim expected payment `Tᵢ(y)` (6.2), p.116: agent `i`'s expected payment when reporting
`y`, the other types being drawn from the prior. -/
noncomputable def interimTransfer (ρ : ∀ i, Measure (Θ i)) (t : ι → (∀ i, Θ i) → ℝ) (i : ι)
    (y : Θ i) : ℝ :=
  ∫ θ, t i (Function.update θ i y) ∂prior ρ

/-- `∫_A uᵢ(a, x) dQᵢ(y)`: the expected utility from decisions of type `x` of agent `i` when
reporting `y`. -/
noncomputable def interimValue (ρ : ∀ i, Measure (Θ i)) (u : ∀ i, A → Θ i → ℝ)
    (q : (∀ i, Θ i) → A) (i : ι) (x y : Θ i) : ℝ :=
  ∫ a, u i a x ∂interimDist ρ q i y

/-- `q` is a decision rule whose interim expectations exist: `q` is measurable (so each `Qᵢ(y)` is
a probability distribution on `A`) and each `uᵢ(·, x)` is integrable against each `Qᵢ(y)`. The book
omits measurability throughout (note 2 to Ch. 2, p.235). -/
def IsDecisionRule (ρ : ∀ i, Measure (Θ i)) (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) :
    Prop :=
  Measurable q ∧ ∀ i (x y : Θ i), Integrable (fun a => u i a x) (interimDist ρ q i y)

/-- The payment rules have interim expectations: for every agent `i` and report `y`, the payment
`tᵢ(y, θ₋ᵢ)` is integrable in `θ₋ᵢ`. -/
def IsTransferRule (ρ : ∀ i, Measure (Θ i)) (t : ι → (∀ i, Θ i) → ℝ) : Prop :=
  ∀ i (y : Θ i), Integrable (fun θ => t i (Function.update θ i y)) (prior ρ)

/-- A direct mechanism all of whose interim expectations exist. -/
def IsMechanism (ρ : ∀ i, Measure (Θ i)) (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A) :
    Prop :=
  IsDecisionRule ρ u M.q ∧ IsTransferRule ρ M.t

/-- Bayesian incentive compatibility (Definition 6.3, p.115): for every agent `i` and all types
`x, y` of agent `i`, the interim expected utility of type `x` from reporting truthfully is at least
that from reporting `y`. -/
def IsBIC (ρ : ∀ i, Measure (Θ i)) (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A) : Prop :=
  ∀ i (x y : Θ i),
    ∫ θ, (u i (M.q (Function.update θ i x)) x - M.t i (Function.update θ i x)) ∂prior ρ ≥
      ∫ θ, (u i (M.q (Function.update θ i y)) x - M.t i (Function.update θ i y)) ∂prior ρ

/-- Interim cyclical monotonicity (Proposition 6.1, p.116): for every agent `i` and every finite
sequence of types `s 0, s 1, …, s m` of agent `i` with `s m = s 0`,
`∑_{κ<m} (∫_A uᵢ(a, s(κ+1)) dQᵢ(s κ) − ∫_A uᵢ(a, s κ) dQᵢ(s κ)) ≤ 0`. -/
def IsInterimCyclicallyMonotone (ρ : ∀ i, Measure (Θ i)) (u : ∀ i, A → Θ i → ℝ)
    (q : (∀ i, Θ i) → A) : Prop :=
  ∀ i (m : ℕ) (s : ℕ → Θ i), s m = s 0 →
    ∑ κ ∈ Finset.range m,
      (interimValue ρ u q i (s (κ + 1)) (s κ) - interimValue ρ u q i (s κ) (s κ)) ≤ 0

/-- Ex post budget balance (Definition 6.5, p.115): `∑ᵢ tᵢ(θ) = 0` for every type vector `θ`. -/
def IsExPostBB (M : DirectMechanism ι Θ A) : Prop :=
  ∀ θ, ∑ i, M.t i θ = 0

/-- Ex ante budget balance (Definition 6.6, p.118): `∫_Θ ∑ᵢ tᵢ(θ) dμ(θ) = 0`, the payment rules
being integrable against the prior (so that the integral exists). -/
def IsExAnteBB (ρ : ∀ i, Measure (Θ i)) (M : DirectMechanism ι Θ A) : Prop :=
  (∀ i, Integrable (M.t i) (prior ρ)) ∧ ∫ θ, ∑ i, M.t i θ ∂prior ρ = 0

/-- Equivalent direct mechanisms (p.118, as for Proposition 3.6): the same decision rule, and for
every agent `i`, all types `θᵢ` and all reports `θᵢ'`, the same expected payment of agent `i`
conditional on type `θᵢ` and report `θᵢ'`. With independent types this conditional expected
payment is `Tᵢ(θᵢ')` whatever `θᵢ` is, so the condition is `T'ᵢ = Tᵢ`. -/
def Equivalent (ρ : ∀ i, Measure (Θ i)) (M M' : DirectMechanism ι Θ A) : Prop :=
  M'.q = M.q ∧ ∀ i (y : Θ i), interimTransfer ρ M'.t i y = interimTransfer ρ M.t i y

end Indep

end MechanismDesign.Correlated
