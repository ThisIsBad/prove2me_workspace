import Mathlib

open MeasureTheory Matrix

namespace RobustPower.StochGap

/-- The mixed-integer domain `ℝ^{n-p}₊ × ℤ^p₊`, up to relabelling coordinates: nonnegative
vectors whose coordinates in `I` are integers (`p = |I|`). -/
def mixedIntDomain {n : ℕ} (I : Set (Fin n)) : Set (Fin n → ℝ) :=
  {x | 0 ≤ x ∧ ∀ i ∈ I, ∃ z : ℤ, x i = z}

/-- Feasibility in the two-stage stochastic problem `Π_Stoch(b)`, (1.1) (p. 3): a first-stage
`x ∈ mixedIntDomain I₁` and an integrable second-stage policy `y : Ω → ℝ^{n₂}` with
`y ω ∈ mixedIntDomain I₂` and `A x + B y(ω) ≥ b(ω)` for every scenario `ω`. -/
def StochFeasible {m n₁ n₂ : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) : Prop :=
  x ∈ mixedIntDomain I₁ ∧ Integrable y μ ∧
    ∀ ω, y ω ∈ mixedIntDomain I₂ ∧ b ω ≤ A *ᵥ x + B *ᵥ y ω

/-- The optimal value `z_Stoch(b)` of (1.1): the infimum, in `EReal`, of
`cᵀx + E_μ[dᵀy(ω)]` over feasible `(x, y)`; it is `⊤` when `Π_Stoch(b)` is infeasible. -/
noncomputable def zStoch {m n₁ n₂ : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (_ : StochFeasible μ A B b I₁ I₂ x y),
    ((c ⬝ᵥ x + ∫ ω, d ⬝ᵥ y ω ∂μ : ℝ) : EReal)

/-- Feasibility in the two-stage robust problem `Π_Rob(b)`, (1.2) (p. 4): one pair `(x, y)`,
`x ∈ mixedIntDomain I₁`, `y ∈ mixedIntDomain I₂`, with `A x + B y ≥ b(ω)` for every `ω`. -/
def RobFeasible {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) : Prop :=
  x ∈ mixedIntDomain I₁ ∧ y ∈ mixedIntDomain I₂ ∧ ∀ ω, b ω ≤ A *ᵥ x + B *ᵥ y

/-- The optimal value `z_Rob(b)` of (1.2): the infimum, in `EReal`, of `cᵀx + dᵀy` over
robust-feasible `(x, y)` (the inner `max_ω dᵀy` equals `dᵀy`, since `d` does not depend on
`ω`); it is `⊤` when `Π_Rob(b)` is infeasible. -/
noncomputable def zRob {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (_ : RobFeasible A B b I₁ I₂ x y),
    ((c ⬝ᵥ x + d ⬝ᵥ y : ℝ) : EReal)

end RobustPower.StochGap
