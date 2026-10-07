import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process

namespace BellmanDP.ContGoldMining

open MeasureTheory

/-- The rate `p′(t) = −p(t) [φ₁ q₁ + φ₂ q₂ + φ₃ q₃]` of the survival probability
(third line of Eqs. (7.2), (12.1)). -/
noncomputable def survivalRate (P : Params) (φ : Control) (t : ℝ) : ℝ :=
  -(survival P φ t * ∑ i, P.q i * φ i t)

/-- Ch. VIII, § 12, Eq. (12.5), p. 234 (and Eq. (8.6), p. 229): the switching function of
decision `i` for horizon `T`, computed along the control `φ`,
`K_i(t) = −q_i ∫ₜᵀ f′(s) ds + p(T) [a_i x(T) + b_i y(T)] − ∫ₜᵀ p′(s) [a_i x(s) + b_i y(s)] ds`,
where `(a_i, b_i) = (r₁, 0), (0, r₂), (r₃, r₄)` for `A, B, C`. -/
noncomputable def switchingFn (P : Params) (x₀ y₀ : ℝ) (φ : Control) (T : ℝ) (i : Fin 3)
    (t : ℝ) : ℝ :=
  -(P.q i * ∫ s in t..T, goldRate P x₀ y₀ φ s)
    + survival P φ T * (P.a i * stateX P x₀ φ T + P.b i * stateY P y₀ φ T)
    - ∫ s in t..T, survivalRate P φ s * (P.a i * stateX P x₀ φ s + P.b i * stateY P y₀ φ s)

/-- The switching function of decision `i` for the horizon `T = ∞` (the case § 12 considers,
p. 233), i.e. Eq. (12.5) with `T = ∞`, where the boundary term `p(T) [a_i x(T) + b_i y(T)]`
tends to `0`:
`K_i(t) = −q_i ∫ₜ^∞ f′(s) ds − ∫ₜ^∞ p′(s) [a_i x(s) + b_i y(s)] ds`. -/
noncomputable def switchingFnInfty (P : Params) (x₀ y₀ : ℝ) (φ : Control) (i : Fin 3)
    (t : ℝ) : ℝ :=
  -(P.q i * ∫ s in Set.Ioi t, goldRate P x₀ y₀ φ s)
    - ∫ s in Set.Ioi t, survivalRate P φ s * (P.a i * stateX P x₀ φ s + P.b i * stateY P y₀ φ s)

/-- Ch. VIII, § 13, Eq. (13.2), p. 234: `C₁ = q₁ r₂ y − q₂ r₁ x`. -/
def C₁ (P : Params) (x y : ℝ) : ℝ := P.q₁ * P.r₂ * y - P.q₂ * P.r₁ * x

/-- Eq. (13.2): `C₂ = q₁ r₄ y − (q₃ r₁ − q₁ r₃) x`. -/
def C₂ (P : Params) (x y : ℝ) : ℝ := P.q₁ * P.r₄ * y - (P.q₃ * P.r₁ - P.q₁ * P.r₃) * x

/-- Eq. (13.2): `C₃ = (q₃ r₂ − q₂ r₄) y − q₂ r₃ x`. -/
def C₃ (P : Params) (x y : ℝ) : ℝ := (P.q₃ * P.r₂ - P.q₂ * P.r₄) * y - P.q₂ * P.r₃ * x

/-- Ch. VIII, § 13, Eq. (13.3), p. 235: `D = q₁ r₂ r₃ + q₂ r₁ r₄ − q₃ r₁ r₂`. -/
def D (P : Params) : ℝ := P.q₁ * P.r₂ * P.r₃ + P.q₂ * P.r₁ * P.r₄ - P.q₃ * P.r₁ * P.r₂

/-- `φ` is an optimal control of the three-choice process for the horizon `T`: it is admissible
and `f(T)` under `φ` is at least `f(T)` under every admissible control. -/
def IsOptimalOn (P : Params) (x₀ y₀ T : ℝ) (φ : Control) : Prop :=
  Admissible φ ∧ ∀ ψ : Control, Admissible ψ → gold P x₀ y₀ ψ T ≤ gold P x₀ y₀ φ T

/-- `φ` is an optimal control of the three-choice process for `T = ∞`: it is admissible and
`f(∞)` under `φ` is at least `f(∞)` under every admissible control. -/
def IsOptimalInfty (P : Params) (x₀ y₀ : ℝ) (φ : Control) : Prop :=
  Admissible φ ∧ ∀ ψ : Control, Admissible ψ → goldInfty P x₀ y₀ ψ ≤ goldInfty P x₀ y₀ φ

end BellmanDP.ContGoldMining
