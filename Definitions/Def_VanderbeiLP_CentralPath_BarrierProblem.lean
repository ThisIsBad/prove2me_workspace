import Mathlib

open Matrix

namespace VanderbeiLP.CentralPath

/-- The primal feasible set `{x : Ax ≤ b, x ≥ 0}` of the LP
`maximize cᵀx subject to Ax ≤ b, x ≥ 0` (Vanderbei, p. 257). -/
def primalFeasibleSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ ∀ i, (A *ᵥ x) i ≤ b i}

/-- The dual feasible set `{y : Aᵀy ≥ c, y ≥ 0}` of the dual LP
`minimize bᵀy subject to Aᵀy ≥ c, y ≥ 0` (Vanderbei, p. 257). -/
def dualFeasibleSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    Set (Fin m → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∀ j, c j ≤ (Aᵀ *ᵥ y) j}

/-- The primal feasible region `{(x, w) : Ax + w = b, x, w ≥ 0}` of (17.1) has nonempty
interior, in the sense fixed by the proof of Theorem 17.2 (p. 265): there is a primal feasible
point `(x̄, w̄)` with `x̄ > 0` and `w̄ > 0` (every component strictly positive). -/
def PrimalStrictlyFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ∃ (x : Fin n → ℝ) (w : Fin m → ℝ), A *ᵥ x + w = b ∧ (∀ j, 0 < x j) ∧ ∀ i, 0 < w i

/-- The dual feasible region `{(y, z) : Aᵀy − z = c, y, z ≥ 0}` of (17.1) has nonempty
interior, in the sense fixed by the proof of Theorem 17.2 (p. 265): there is a dual feasible
point `(ȳ, z̄)` with `ȳ > 0` and `z̄ > 0`. -/
def DualStrictlyFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) : Prop :=
  ∃ (y : Fin m → ℝ) (z : Fin n → ℝ), Aᵀ *ᵥ y - z = c ∧ (∀ i, 0 < y i) ∧ ∀ j, 0 < z j

/-- The logarithmic barrier function (17.7):
`f(x, w) = cᵀx + μ ∑ⱼ log xⱼ + μ ∑ᵢ log wᵢ`.
It is only meaningful for `x > 0`, `w > 0`; every use below restricts to that domain. -/
noncomputable def barrierFunction {m n : ℕ} (c : Fin n → ℝ) (μ : ℝ) (x : Fin n → ℝ)
    (w : Fin m → ℝ) : ℝ :=
  c ⬝ᵥ x + μ * ∑ j, Real.log (x j) + μ * ∑ i, Real.log (w i)

/-- `(x, w)` is a solution of the barrier problem (17.2)
`maximize cᵀx + μ ∑ⱼ log xⱼ + μ ∑ᵢ log wᵢ subject to Ax + w = b`:
it lies in the domain of the barrier (`Ax + w = b`, `x > 0`, `w > 0`) and maximizes the barrier
function (17.7) over that domain. -/
def IsBarrierSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (μ : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) : Prop :=
  A *ᵥ x + w = b ∧ (∀ j, 0 < x j) ∧ (∀ i, 0 < w i) ∧
    ∀ (x' : Fin n → ℝ) (w' : Fin m → ℝ), A *ᵥ x' + w' = b → (∀ j, 0 < x' j) →
      (∀ i, 0 < w' i) → barrierFunction c μ x' w' ≤ barrierFunction c μ x w

/-- `(x, w, y, z)` solves the primal–dual central-path system (17.6)
`Ax + w = b, Aᵀy − z = c, XZe = μe, YWe = μe`, with `x, w, y, z > 0`
(the domain of the barrier problem, from which (17.6) is derived on p. 263). -/
def IsCentralPathPoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (μ : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) (y : Fin m → ℝ)
    (z : Fin n → ℝ) : Prop :=
  A *ᵥ x + w = b ∧ Aᵀ *ᵥ y - z = c ∧ (∀ j, x j * z j = μ) ∧ (∀ i, y i * w i = μ) ∧
    (∀ j, 0 < x j) ∧ (∀ i, 0 < w i) ∧ (∀ i, 0 < y i) ∧ ∀ j, 0 < z j

end VanderbeiLP.CentralPath
