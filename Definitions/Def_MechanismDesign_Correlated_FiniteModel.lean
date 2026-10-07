import Mathlib

namespace MechanismDesign.Correlated

namespace FiniteTypes

/-!
Bayesian mechanism design with finite, possibly correlated types (Börgers, *An Introduction to the
Theory of Mechanism Design*, §6.2 and §6.4, pp.114–127).

Agents form a finite set `ι`; agent `i`'s type set `Θ i` is finite; the alternatives form an
arbitrary set `A`. A distribution on `Θ = ∏ᵢ Θ i` is a function `ν : Θ → ℝ`. The standing assumption
of §6.4 (p.119) is that the common prior `μ` gives every type vector positive probability.

A type vector of the other agents `θ₋ᵢ ∈ Θ₋ᵢ` is represented by any full type vector `θ`; the
functions below depend on `θ` only through `θ₋ᵢ`, because coordinate `i` is overwritten by
`Function.update θ i x`, or the sum ranges over the fibre `{θ | θ i = x}`, which is in bijection
with `Θ₋ᵢ`.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*} [∀ i, Fintype (Θ i)]
  [∀ i, DecidableEq (Θ i)]

/-- `ν` is a probability distribution on `Θ` giving every type vector positive probability. -/
def IsFullSupportDist (ν : (∀ i, Θ i) → ℝ) : Prop :=
  (∀ θ, 0 < ν θ) ∧ ∑ θ, ν θ = 1

/-- The probability `ν(θᵢ = x)` that agent `i`'s type is `x`. -/
def typeProb (ν : (∀ i, Θ i) → ℝ) (i : ι) (x : Θ i) : ℝ :=
  ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = x), ν θ

/-- The conditional probability `ν(θ₋ᵢ | x)` of the other agents' types `θ₋ᵢ` (read off `θ`) given
that agent `i`'s type is `x`. -/
noncomputable def condProb (ν : (∀ i, Θ i) → ℝ) (i : ι) (x : Θ i) (θ : ∀ j, Θ j) : ℝ :=
  ν (Function.update θ i x) / typeProb ν i x

/-- The conditional expectation `∑_{θ₋ᵢ ∈ Θ₋ᵢ} g(x, θ₋ᵢ) ν(θ₋ᵢ | x)` of `g` given that agent `i`'s
type is `x`; the sum ranges over the type vectors `θ` with `θ i = x`. -/
noncomputable def condExp (ν : (∀ i, Θ i) → ℝ) (i : ι) (x : Θ i) (g : (∀ j, Θ j) → ℝ) : ℝ :=
  ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = x), g θ * condProb ν i x θ

/-- A direct mechanism (Definition 6.2, p.115): a decision rule `q : Θ → A` and a payment rule
`t i : Θ → ℝ` for every agent `i`. -/
structure DirectMechanism (ι : Type*) (Θ : ι → Type*) (A : Type*) where
  /-- the decision rule `q` -/
  q : (∀ i, Θ i) → A
  /-- the payment rule `t i` of agent `i` -/
  t : ι → (∀ i, Θ i) → ℝ

variable {A : Type*}

/-- Bayesian incentive compatibility (Definition 6.3, p.115) with respect to the prior `μ` and
utilities `u i a θᵢ - tᵢ`: for every agent `i` and all types `x, y` of agent `i`,
`∑_{θ₋ᵢ} (uᵢ(q(x, θ₋ᵢ), x) − tᵢ(x, θ₋ᵢ)) μ(θ₋ᵢ | x) ≥ ∑_{θ₋ᵢ} (uᵢ(q(y, θ₋ᵢ), x) − tᵢ(y, θ₋ᵢ)) μ(θ₋ᵢ | x)`. -/
def IsBIC (μ : (∀ i, Θ i) → ℝ) (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A) : Prop :=
  ∀ i (x y : Θ i),
    condExp μ i x (fun θ => u i (M.q θ) x - M.t i θ) ≥
      condExp μ i x (fun θ => u i (M.q (Function.update θ i y)) x - M.t i (Function.update θ i y))

/-- Ex post budget balance (Definition 6.5, p.115): `∑ᵢ tᵢ(θ) = 0` for every type vector `θ`. -/
def IsExPostBB (M : DirectMechanism ι Θ A) : Prop :=
  ∀ θ, ∑ i, M.t i θ = 0

/-- Ex ante budget balance (Definition 6.6, p.118): `∑_θ μ(θ) ∑ᵢ tᵢ(θ) = 0`. -/
def IsExAnteBB (μ : (∀ i, Θ i) → ℝ) (M : DirectMechanism ι Θ A) : Prop :=
  ∑ θ, μ θ * ∑ i, M.t i θ = 0

/-- The Crémer–McLean condition (Definition 6.7, p.120): there are no agent `i`, type `x` of `i`
and nonnegative weights `λ(y)`, `y ∈ Θᵢ \ {x}`, with
`μ(θ₋ᵢ | x) = ∑_{y ∈ Θᵢ \ {x}} λ(y) μ(θ₋ᵢ | y)` for all `θ₋ᵢ`. (The weights are given on all of
`Θᵢ`; the value at `x` is never used.) -/
def CremerMcLean (μ : (∀ i, Θ i) → ℝ) : Prop :=
  ¬ ∃ (i : ι) (x : Θ i) (w : Θ i → ℝ), (∀ y, y ≠ x → 0 ≤ w y) ∧
    ∀ θ : ∀ j, Θ j, condProb μ i x θ = ∑ y ∈ Finset.univ.erase x, w y * condProb μ i y θ

/-- The identifiability condition (Definition 6.8, p.126): for every distribution `ν ≠ μ` on `Θ`
with `ν(θ) > 0` for all `θ`, there are an agent `i` and a type `x` of `i` such that for every
collection of nonnegative coefficients `(λ_y)_{y ∈ Θᵢ}` there is some `θ₋ᵢ` with
`ν(θ₋ᵢ | x) ≠ ∑_{y ∈ Θᵢ} λ_y μ(θ₋ᵢ | y)`. -/
def Identifiable (μ : (∀ i, Θ i) → ℝ) : Prop :=
  ∀ ν : (∀ i, Θ i) → ℝ, IsFullSupportDist ν → ν ≠ μ →
    ∃ (i : ι) (x : Θ i), ∀ w : Θ i → ℝ, (∀ y, 0 ≤ w y) →
      ∃ θ : ∀ j, Θ j, condProb ν i x θ ≠ ∑ y, w y * condProb μ i y θ

end FiniteTypes

end MechanismDesign.Correlated
