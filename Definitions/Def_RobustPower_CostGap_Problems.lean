import Mathlib
import Definitions.Def_RobustPower_StochGap_Problems

open MeasureTheory Matrix

namespace RobustPower.CostGap

/-- Feasibility in the two-stage stochastic problem `Π_Stoch(b, d)`, (1.4) (p. 4): a first-stage
`x ∈ RobustPower.StochGap.mixedIntDomain I₁` and an integrable second-stage policy `y : Ω → ℝ^{n₂}` whose cost
`ω ↦ d(ω)ᵀy(ω)` is integrable, with `y ω ∈ RobustPower.StochGap.mixedIntDomain I₂` and `A x + B y(ω) ≥ b(ω)` for
every scenario `ω`. -/
def StochFeasibleBD {m n₁ n₂ : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (d : Ω → Fin n₂ → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (x : Fin n₁ → ℝ)
    (y : Ω → Fin n₂ → ℝ) : Prop :=
  x ∈ RobustPower.StochGap.mixedIntDomain I₁ ∧ Integrable y μ ∧ Integrable (fun ω => d ω ⬝ᵥ y ω) μ ∧
    ∀ ω, y ω ∈ RobustPower.StochGap.mixedIntDomain I₂ ∧ b ω ≤ A *ᵥ x + B *ᵥ y ω

/-- The optimal value `z_Stoch(b, d)` of (1.4): the infimum, in `EReal`, of
`cᵀx + E_μ[d(ω)ᵀy(ω)]` over feasible `(x, y)`; it is `⊤` when `Π_Stoch(b, d)` is infeasible. -/
noncomputable def zStochBD {m n₁ n₂ : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (_ : StochFeasibleBD μ A B b d I₁ I₂ x y),
    ((c ⬝ᵥ x + ∫ ω, d ω ⬝ᵥ y ω ∂μ : ℝ) : EReal)

/-- Feasibility in the two-stage robust problem `Π_Rob(b, d)`, (1.5) (p. 5): one pair `(x, y)`,
`x ∈ RobustPower.StochGap.mixedIntDomain I₁`, `y ∈ RobustPower.StochGap.mixedIntDomain I₂`, with `A x + B y ≥ b(ω)` for every `ω`. -/
def RobFeasibleBD {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) : Prop :=
  x ∈ RobustPower.StochGap.mixedIntDomain I₁ ∧ y ∈ RobustPower.StochGap.mixedIntDomain I₂ ∧ ∀ ω, b ω ≤ A *ᵥ x + B *ᵥ y

/-- The optimal value `z_Rob(b, d)` of (1.5): the infimum, in `EReal`, of
`cᵀx + sup_ω d(ω)ᵀy` over robust-feasible `(x, y)`. The worst-case second-stage cost is an
`EReal` supremum, so it may be `+∞`; the value is `⊤` when `Π_Rob(b, d)` is infeasible. -/
noncomputable def zRobBD {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Ω → Fin m → ℝ)
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (_ : RobFeasibleBD A B b I₁ I₂ x y),
    ((c ⬝ᵥ x : ℝ) : EReal) + ⨆ ω, ((d ω ⬝ᵥ y : ℝ) : EReal)

end RobustPower.CostGap
