import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi

set_option autoImplicit false

namespace ChanceDetEquiv.PModel

open MeasureTheory
open scoped BigOperators

/-- The fixed matrix, random right-hand side and objective, confidence levels, and aspiration value in the P model. -/
structure Model (Ω : Type*) (m n : ℕ) [MeasurableSpace Ω] where
  P : Measure Ω
  A : Matrix (Fin m) (Fin n) ℝ
  b : Ω → Fin m → ℝ
  c : Ω → Fin n → ℝ
  α : Fin m → ℝ
  z0 : ℝ

/-- The paper's interior confidence levels. -/
def Confidence {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (d : Model Ω m n) : Prop :=
  ∀ i, (1 / 2 : ℝ) < d.α i ∧ d.α i < 1

/-- Square integrability of the components needed by all moments in (30), (34), and (39b), plus the paper's lack of correlation between the random objective and right-hand side. -/
def MomentAssumptions {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (d : Model Ω m n) : Prop :=
  (∀ k, MemLp (fun ω => d.b ω k) 2 d.P) ∧
  (∀ j, MemLp (fun ω => d.c ω j) 2 d.P) ∧
  (∀ j k, MemLp (fun ω => d.c ω j * d.b ω k) 2 d.P) ∧
  (∀ j k, (∫ ω, d.c ω j * d.b ω k ∂d.P) =
    (∫ ω, d.c ω j ∂d.P) * (∫ ω, d.b ω k ∂d.P))

/-- `μ_b`, equation (19b). -/
noncomputable def meanB {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (d : Model Ω m n) : Fin m → ℝ :=
  fun k => ∫ ω, d.b ω k ∂d.P

/-- `μ_c`, equation (19b). -/
noncomputable def meanC {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (d : Model Ω m n) : Fin n → ℝ :=
  fun j => ∫ ω, d.c ω j ∂d.P

/-- The deterministic mean objective `μ_c' D μ_b`. -/
noncomputable def meanObjective {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) (D : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ j : Fin n, meanC d j * (D.mulVec (meanB d)) j

/-- `a_i' D b(ω) - b_i(ω)`, the random residual in (30). -/
def rowResidual {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) (ω : Ω) : ℝ :=
  (d.A.mulVec (D.mulVec (d.b ω))) i - d.b ω i

/-- The paper's standing normal-law assumption on each row residual for every decision matrix. -/
def NormalRows {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) : Prop :=
  ∀ (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ),
    ∃ μ : ℝ, ∃ variance : NNReal,
      Measure.map (rowResidual d i D) d.P = ProbabilityTheory.gaussianReal μ variance

/-- `σ_i²(D) = E(a_i'Db - b_i)²`, the raw second moment in (30). -/
noncomputable def sigmaSq {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∫ ω, rowResidual d i D ω ^ 2 ∂d.P

/-- `μ_i(D) = μ_{b_i} - a_i'D μ_b` from (30). -/
noncomputable def muRow {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  meanB d i - (d.A.mulVec (D.mulVec (meanB d))) i

/-- `V(D) = E(c'Db - z₀)²`, equation (34). -/
noncomputable def V {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) (D : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∫ ω, ((∑ j : Fin n, d.c ω j * (D.mulVec (d.b ω)) j) - d.z0) ^ 2 ∂d.P

/-- The barred mean residual `t μ_{b_i} - a_i' D̄ μ_b`, equation (39b). -/
noncomputable def muBar {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) (i : Fin m) (Dbar : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) : ℝ :=
  t * meanB d i - (d.A.mulVec (Dbar.mulVec (meanB d))) i

/-- `σ̄_i²(D̄,t) = E(a_i'D̄b - t b_i)²`, the raw second moment in (39b). -/
noncomputable def sigmaBarSq {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) (i : Fin m) (Dbar : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) : ℝ :=
  ∫ ω, ((d.A.mulVec (Dbar.mulVec (d.b ω))) i - t * d.b ω i) ^ 2 ∂d.P

/-- `V̄(D̄,t) = E(c'D̄b - t z₀)²`, equation (39b). -/
noncomputable def Vbar {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) (Dbar : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) : ℝ :=
  ∫ ω, ((∑ j : Fin n, d.c ω j * (Dbar.mulVec (d.b ω)) j) - t * d.z0) ^ 2 ∂d.P

/-- The constant `K_{α_i}` of (27)–(39), from the inverse standard normal CDF. -/
noncomputable def K {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) (i : Fin m) : ℝ := Cohen2019.Robust.PhiInvReal (d.α i)

/-- Coordinates are `(D, v, v₀, w₀)`. -/
abbrev Point38 (m n : ℕ) := Matrix (Fin n) (Fin m) ℝ × (Fin m → ℝ) × ℝ × ℝ
/-- Coordinates are `(D̄, v̄, v̄₀, w̄₀, t)`. -/
abbrev Point39 (m n : ℕ) := Matrix (Fin n) (Fin m) ℝ × (Fin m → ℝ) × ℝ × ℝ × ℝ

/-- The corrected constraints of program (38), with the paper's `w₀ > 0`. -/
noncomputable def feasible38 {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) : Set (Point38 m n) :=
  {p | meanObjective d p.1 - p.2.2.1 ≥ d.z0 ∧
    -V d p.1 + p.2.2.2 ^ 2 ≥ 0 ∧
    (∀ i, muRow d i p.1 - p.2.1 i ≥ 0 ∧
      -(K d i ^ 2) * sigmaSq d i p.1 + K d i ^ 2 * muRow d i p.1 ^ 2 +
        (p.2.1 i) ^ 2 ≥ 0 ∧ 0 ≤ p.2.1 i) ∧
    0 < p.2.2.2}

/-- The complete constraints of (39), including the boundary `t = 0`. -/
noncomputable def feasible39 {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) : Set (Point39 m n) :=
  {p | meanObjective d p.1 - p.2.2.1 ≥ p.2.2.2.2 * d.z0 ∧
    -Vbar d p.1 p.2.2.2.2 + p.2.2.2.1 ^ 2 ≥ 0 ∧
    (∀ i, muBar d i p.1 p.2.2.2.2 - p.2.1 i ≥ 0 ∧
      -(K d i ^ 2) * sigmaBarSq d i p.1 p.2.2.2.2 +
        K d i ^ 2 * muBar d i p.1 p.2.2.2.2 ^ 2 +
        (p.2.1 i) ^ 2 ≥ 0 ∧ 0 ≤ p.2.1 i) ∧
    p.2.2.2.1 = 1 ∧ 0 ≤ p.2.2.2.2}

/-- The normalized substitution (39a), also scaling the objective numerator. -/
noncomputable def forward {m n : ℕ} (p : Point38 m n) : Point39 m n :=
  let t := 1 / p.2.2.2
  (t • p.1, t • p.2.1, t * p.2.2.1, t * p.2.2.2, t)

/-- The inverse of (39a) for positive `t`. -/
noncomputable def backward {m n : ℕ} (p : Point39 m n) : Point38 m n :=
  let t := p.2.2.2.2
  (t⁻¹ • p.1, t⁻¹ • p.2.1, t⁻¹ * p.2.2.1, t⁻¹)

/-- The fractional objective in (38). -/
noncomputable def value38 {m n : ℕ} (p : Point38 m n) : ℝ := p.2.2.1 / p.2.2.2
/-- The linear objective in (39). -/
def value39 {m n : ℕ} (p : Point39 m n) : ℝ := p.2.2.1

/-- Extended-real values attainable in (38), so an unbounded supremum is represented. -/
noncomputable def values38 {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) : Set EReal :=
  (fun p : Point38 m n => (value38 p : EReal)) '' feasible38 d

/-- Extended-real values attainable in (39), including values with `t = 0`. -/
noncomputable def values39 {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) : Set EReal :=
  (fun p : Point39 m n => (value39 p : EReal)) '' feasible39 d

end ChanceDetEquiv.PModel
