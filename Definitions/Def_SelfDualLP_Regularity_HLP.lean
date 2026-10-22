import Definitions.Def_SelfDualLP_Regularity_LPData

open Matrix

namespace SelfDualLP.Regularity

/-- A point `(y,x,τ,θ,s,κ)` of the paper's homogeneous program (HLP). -/
structure HLPPoint (m n : ℕ) where
  y : Fin m → ℝ
  x : Fin n → ℝ
  τ : ℝ
  θ : ℝ
  s : Fin n → ℝ
  κ : ℝ

/-- `b̄ = b - Ax⁰` from (5). -/
def bBar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x₀ : Fin n → ℝ) : Fin m → ℝ :=
  b - A *ᵥ x₀

/-- `c̄ = c - Aᵀy⁰ - s⁰` from (5). -/
def cBar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ) : Fin n → ℝ :=
  c - Aᵀ *ᵥ y₀ - s₀

/-- `z̄ = cᵀx⁰ + 1 - bᵀy⁰` from (5). -/
def zBar {m n : ℕ} (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) : ℝ :=
  c ⬝ᵥ x₀ + 1 - b ⬝ᵥ y₀

/-- The objective `((x⁰)ᵀs⁰ + 1)θ` of (HLP). -/
def HLPObjective {m n : ℕ} (x₀ s₀ : Fin n → ℝ) (w : HLPPoint m n) : ℝ :=
  (x₀ ⬝ᵥ s₀ + 1) * w.θ

/-- Feasibility for (HLP), including exact definitions of the slacks `s` and `κ`.
The four equations follow rows (1)--(4) on p. 56 in the order `(y,x,τ,θ)`. -/
def HLPFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (w : HLPPoint m n) : Prop :=
  A *ᵥ w.x - w.τ • b + w.θ • bBar A b x₀ = 0 ∧
  w.s = -(Aᵀ *ᵥ w.y) + w.τ • c - w.θ • cBar A c y₀ s₀ ∧
  w.κ = b ⬝ᵥ w.y - c ⬝ᵥ w.x + zBar b c x₀ y₀ * w.θ ∧
  -(bBar A b x₀ ⬝ᵥ w.y) + cBar A c y₀ s₀ ⬝ᵥ w.x -
      zBar b c x₀ y₀ * w.τ = -(x₀ ⬝ᵥ s₀) - 1 ∧
  (∀ j, 0 ≤ w.x j) ∧ 0 ≤ w.τ ∧ (∀ j, 0 ≤ w.s j) ∧ 0 ≤ w.κ

/-- The strictly feasible set `Fₕ°`: the nonnegative fields are strictly positive. -/
def HLPStrictlyFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (w : HLPPoint m n) : Prop :=
  HLPFeasible A b c x₀ y₀ s₀ w ∧
    (∀ j, 0 < w.x j) ∧ 0 < w.τ ∧ (∀ j, 0 < w.s j) ∧ 0 < w.κ

/-- Optimality means minimizing the HLP objective over all of `Fₕ`. -/
def IsHLPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (w : HLPPoint m n) : Prop :=
  HLPFeasible A b c x₀ y₀ s₀ w ∧
    ∀ v, HLPFeasible A b c x₀ y₀ s₀ v →
      HLPObjective x₀ s₀ w ≤ HLPObjective x₀ s₀ v

/-- The paper's choice (7): `y⁰ = 0`, `x⁰ = s⁰ = e`. -/
def IsSelfComplementary {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (w : HLPPoint m n) : Prop :=
  IsHLPOptimal A b c (fun _ => 1) (fun _ => 0) (fun _ => 1) w

end SelfDualLP.Regularity
