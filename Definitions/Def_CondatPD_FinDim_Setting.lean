import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_InertialFB_IFB_ConvexAnalysis

open InnerProductSpace

namespace CondatPD.FinDim

/-! Objects of Condat (2013), §2–§3 and §5, and the operators `P`, `P′`, `T` of the proof of
Theorem 3.3 (§4). Γ₀ is `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`, proximity operators
are maps satisfying `ThreeOpSplitting.ConvexRates.IsProx`, and `∂J` is
`InertialFB.IFB.IsSubgradient`. -/

/-- The Fenchel–Rockafellar conjugate `J*(s) = sup_{s'} [⟨s, s'⟩ − J(s')]` (p. 2), an extended
real supremum. -/
noncomputable def conj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (J : E → EReal) (s : E) : EReal :=
  ⨆ s' : E, ((⟪s, s'⟫_ℝ : ℝ) : EReal) - J s'

/-- The smooth term of (2): `F` is convex, differentiable on `X`, and `∇F` is `β`-Lipschitz for
some `β ∈ [0, +∞[`. -/
def IsSmoothTerm {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (β : ℝ) (F : X → ℝ) : Prop :=
  ConvexOn ℝ Set.univ F ∧ Differentiable ℝ F ∧ 0 ≤ β ∧
    ∀ x x' : X, ‖gradient F x - gradient F x'‖ ≤ β * ‖x - x'‖

/-- `(xh, yh)` solves the inclusion (6):
`0 ∈ ∂G(xh) + L* yh + ∇F(xh)` and `0 ∈ −L xh + ∂H*(yh)`, written as
`−L* yh − ∇F(xh) ∈ ∂G(xh)` and `L xh ∈ ∂H*(yh)`. -/
def IsPDSolution {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y) (xh : X) (yh : Y) : Prop :=
  InertialFB.IFB.IsSubgradient G xh (-(ContinuousLinearMap.adjoint L yh) - gradient F xh) ∧
    InertialFB.IFB.IsSubgradient (conj H) yh (L xh)

/-- `(x, y)` is a run of Algorithm 3.1, (9), with proximity maps `PG = prox_{τG}`,
`PH = prox_{σH*}`, relaxation parameters `ρ` and error terms `eF, eG, eH`; the initial estimate
`(x 0, y 0)` is arbitrary. -/
def IsAlg31Run {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → ℝ) (PG : X → X) (PH : Y → Y) (τ σ : ℝ) (L : X →L[ℝ] Y) (ρ : ℕ → ℝ)
    (eF eG : ℕ → X) (eH : ℕ → Y) (x : ℕ → X) (y : ℕ → Y) : Prop :=
  ∀ n : ℕ,
    let xt := PG (x n - τ • (gradient F (x n) + eF n) - τ • ContinuousLinearMap.adjoint L (y n))
      + eG n
    let yt := PH (y n + σ • L ((2 : ℝ) • xt - x n)) + eH n
    x (n + 1) = ρ n • xt + (1 - ρ n) • x n ∧ y (n + 1) = ρ n • yt + (1 - ρ n) • y n

/-- `(x, y)` is a run of Algorithm 3.2, (10): the dual step comes first, and the primal step uses
the over-relaxed dual point `2 ỹₙ₊₁ − yₙ`. -/
def IsAlg32Run {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → ℝ) (PG : X → X) (PH : Y → Y) (τ σ : ℝ) (L : X →L[ℝ] Y) (ρ : ℕ → ℝ)
    (eF eG : ℕ → X) (eH : ℕ → Y) (x : ℕ → X) (y : ℕ → Y) : Prop :=
  ∀ n : ℕ,
    let yt := PH (y n + σ • L (x n)) + eH n
    let xt := PG (x n - τ • (gradient F (x n) + eF n)
      - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • yt - y n)) + eG n
    x (n + 1) = ρ n • xt + (1 - ρ n) • x n ∧ y (n + 1) = ρ n • yt + (1 - ρ n) • y n

/-- The quadratic form `⟨z, P z⟩_I` of the operator `P` of (20), at `z = (x, y)`:
`⟨x, x/τ − L* y⟩ + ⟨y, −L x + y/σ⟩`. -/
noncomputable def qP {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (τ σ : ℝ) (L : X →L[ℝ] Y) (x : X) (y : Y) : ℝ :=
  ⟪x, τ⁻¹ • x - ContinuousLinearMap.adjoint L y⟫_ℝ + ⟪y, -(L x) + σ⁻¹ • y⟫_ℝ

/-- The quadratic form `⟨z, P′ z⟩_I` of the operator `P′` of (44), at `z = (x, y)`:
`⟨x, x/τ + L* y⟩ + ⟨y, L x + y/σ⟩`. -/
noncomputable def qP' {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (τ σ : ℝ) (L : X →L[ℝ] Y) (x : X) (y : Y) : ℝ :=
  ⟪x, τ⁻¹ • x + ContinuousLinearMap.adjoint L y⟫_ℝ + ⟪y, L x + σ⁻¹ • y⟫_ℝ

/-- The operator `P : (x, y) ↦ (x/τ − L* y, −L x + y/σ)` of (20), as a map on `X × Y`. -/
noncomputable def opP {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (τ σ : ℝ) (L : X →L[ℝ] Y) (z : X × Y) : X × Y :=
  (τ⁻¹ • z.1 - ContinuousLinearMap.adjoint L z.2, -(L z.1) + σ⁻¹ • z.2)

/-- The operator `T` of the proof of Theorem 3.3 (p. 12): steps 1. and 2. of Algorithm 3.1 with
`F = 0` and no error terms, `T(x, y) = (x̃, ỹ)` with `x̃ = prox_{τG}(x − τ L* y)` and
`ỹ = prox_{σH*}(y + σ L(2x̃ − x))`. -/
noncomputable def stepT {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (PG : X → X) (PH : Y → Y) (τ σ : ℝ) (L : X →L[ℝ] Y) (z : X × Y) : X × Y :=
  let xt := PG (z.1 - τ • ContinuousLinearMap.adjoint L z.2)
  (xt, PH (z.2 + σ • L ((2 : ℝ) • xt - z.1)))

/-! §5: `m` composite terms `Hᵢ ∘ Lᵢ`, `Lᵢ : X → Yᵢ`. -/

/-- `(xh, yh₁, …, yhₘ)` solves (48): `0 ∈ ∂G(xh) + Σᵢ Lᵢ* yhᵢ + ∇F(xh)` and, for every `i`,
`0 ∈ −Lᵢ xh + ∂Hᵢ*(yhᵢ)`. -/
def IsPDSolutionM {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {m : ℕ} {Y : Fin m → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, InnerProductSpace ℝ (Y i)]
    [∀ i, CompleteSpace (Y i)]
    (F : X → ℝ) (G : X → EReal) (H : ∀ i, Y i → EReal) (L : ∀ i, X →L[ℝ] Y i)
    (xh : X) (yh : ∀ i, Y i) : Prop :=
  InertialFB.IFB.IsSubgradient G xh
      (-(∑ i, ContinuousLinearMap.adjoint (L i) (yh i)) - gradient F xh) ∧
    ∀ i, InertialFB.IFB.IsSubgradient (conj (H i)) (yh i) (L i xh)

/-- `(x, y)` is a run of Algorithm 5.1, (55), with `PG = prox_{τG}` and `PH i = prox_{σHᵢ*}`. -/
def IsAlg51Run {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {m : ℕ} {Y : Fin m → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, InnerProductSpace ℝ (Y i)]
    [∀ i, CompleteSpace (Y i)]
    (F : X → ℝ) (PG : X → X) (PH : ∀ i, Y i → Y i) (τ σ : ℝ) (L : ∀ i, X →L[ℝ] Y i)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → ∀ i, Y i) (x : ℕ → X) (y : ℕ → ∀ i, Y i) : Prop :=
  ∀ n : ℕ,
    let xt := PG (x n - τ • (gradient F (x n) + eF n)
      - τ • ∑ i, ContinuousLinearMap.adjoint (L i) (y n i)) + eG n
    x (n + 1) = ρ n • xt + (1 - ρ n) • x n ∧
      ∀ i, y (n + 1) i =
        ρ n • (PH i (y n i + σ • L i ((2 : ℝ) • xt - x n)) + eH n i) + (1 - ρ n) • y n i

/-- `(x, y)` is a run of Algorithm 5.2, (56), with step 3 in its indexed form
`τ Σᵢ Lᵢ*(2ỹ_{i,n+1} − y_{i,n})`. -/
def IsAlg52Run {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {m : ℕ} {Y : Fin m → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, InnerProductSpace ℝ (Y i)]
    [∀ i, CompleteSpace (Y i)]
    (F : X → ℝ) (PG : X → X) (PH : ∀ i, Y i → Y i) (τ σ : ℝ) (L : ∀ i, X →L[ℝ] Y i)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → ∀ i, Y i) (x : ℕ → X) (y : ℕ → ∀ i, Y i) : Prop :=
  ∀ n : ℕ,
    let yt : ∀ i, Y i := fun i => PH i (y n i + σ • L i (x n)) + eH n i
    let xt := PG (x n - τ • (gradient F (x n) + eF n)
      - τ • ∑ i, ContinuousLinearMap.adjoint (L i) ((2 : ℝ) • yt i - y n i)) + eG n
    (∀ i, y (n + 1) i = ρ n • yt i + (1 - ρ n) • y n i) ∧
      x (n + 1) = ρ n • xt + (1 - ρ n) • x n

end CondatPD.FinDim
