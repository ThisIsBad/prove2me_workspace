import Mathlib

open InnerProductSpace

namespace ThreeOpSplitting.Accel

/-- A set-valued operator `A : H → 2^H` is monotone if `⟪x - y, u - v⟫ ≥ 0`
whenever `u ∈ A x` and `v ∈ A y`. -/
def IsMonotoneOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) : Prop :=
  ∀ x y u v : H, u ∈ A x → v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ

/-- A monotone operator is maximal monotone if its graph is not properly contained in the
graph of another monotone operator. -/
def IsMaximalMonotone {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) : Prop :=
  IsMonotoneOp A ∧ ∀ A' : H → Set H, IsMonotoneOp A' → (∀ x, A x ⊆ A' x) → A' = A

/-- A set-valued operator `B` is `μ`-strongly monotone if
`⟪x - y, u - v⟫ ≥ μ ‖x - y‖²` whenever `u ∈ B x` and `v ∈ B y`. The sign of `μ` is imposed
separately wherever it is used (the paper allows `μ = 0` for `B`). -/
def IsStronglyMonotoneOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : ℝ) (B : H → Set H) : Prop :=
  ∀ x y u v : H, u ∈ B x → v ∈ B y → μ * ‖x - y‖ ^ 2 ≤ ⟪x - y, u - v⟫_ℝ

/-- A single-valued operator `C : H → H` is monotone if `⟪x - y, C x - C y⟫ ≥ 0` for all
`x, y`. -/
def IsMonotoneFun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : H → H) : Prop :=
  ∀ x y : H, 0 ≤ ⟪x - y, C x - C y⟫_ℝ

/-- A single-valued operator `C : H → H` is `μ`-strongly monotone if
`⟪x - y, C x - C y⟫ ≥ μ ‖x - y‖²` for all `x, y`. -/
def IsStronglyMonotoneFun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : ℝ) (C : H → H) : Prop :=
  ∀ x y : H, μ * ‖x - y‖ ^ 2 ≤ ⟪x - y, C x - C y⟫_ℝ

/-- A single-valued operator `C` is `β`-cocoercive if
`β ‖C x - C y‖² ≤ ⟪C x - C y, x - y⟫` for all `x, y` (the positivity `β > 0` is a separate
hypothesis wherever it is needed). -/
def IsCocoercive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (β : ℝ) (C : H → H) : Prop :=
  ∀ x y : H, β * ‖C x - C y‖ ^ 2 ≤ ⟪C x - C y, x - y⟫_ℝ

/-- A single-valued operator `C` is `L`-Lipschitz if `‖C x - C y‖ ≤ L ‖x - y‖` for all
`x, y`. -/
def IsLipschitzOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (L : ℝ) (C : H → H) : Prop :=
  ∀ x y : H, ‖C x - C y‖ ≤ L * ‖x - y‖

/-- The set of zeros `zer(M) = {x | 0 ∈ M x}` of a set-valued operator. -/
def zer {H : Type*} [Zero H] (M : H → Set H) : Set H := {x | (0 : H) ∈ M x}

/-- The sum `A + B + C` of two set-valued operators and a single-valued operator:
`(A + B + C) x = {a + b + C x | a ∈ A x, b ∈ B x}`. -/
def opSum {H : Type*} [Add H] (A B : H → Set H) (C : H → H) : H → Set H :=
  fun x => {w | ∃ a ∈ A x, ∃ b ∈ B x, w = a + b + C x}

/-- `J` is (a choice of) the resolvent `J_{γA} = (I + γA)⁻¹`: for every `x`,
`γ⁻¹ (x - J x) ∈ A (J x)`, i.e. `x ∈ J x + γ A (J x)`. For maximal monotone `A` and `γ > 0`
such a map exists (Minty) and is unique. -/
def IsResolvent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (A : H → Set H) (J : H → H) : Prop :=
  ∀ x : H, γ⁻¹ • (x - J x) ∈ A (J x)

/-- `J : ℝ → H → H` is a family of resolvents of `A`: for every stepsize `γ > 0`, `J γ` is the
resolvent `J_{γA}`. Values of `J γ` for `γ ≤ 0` are unconstrained and never used. -/
def IsResolventFamily {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (J : ℝ → H → H) : Prop :=
  ∀ γ : ℝ, 0 < γ → IsResolvent γ A (J γ)

end ThreeOpSplitting.Accel
