import Mathlib

namespace StochasticProg.Recourse

/-- First-stage data for a simple-recourse instance, `W = [I,-I]` (p. 113): the
recourse matrix itself plays no further role once `q⁺, q⁻` are separated, so only
the first-stage data and the split cost vectors are kept. -/
structure SimpleRecourseInstance (n1 m1 m2 : ℕ) where
  A : Matrix (Fin m1) (Fin n1) ℝ
  b : Fin m1 → ℝ
  c : Fin n1 → ℝ
  T : Matrix (Fin m2) (Fin n1) ℝ
  qplus : Fin m2 → ℝ
  qminus : Fin m2 → ℝ

variable {n1 m1 m2 : ℕ}

/-- `q_i = q⁺_i + q⁻_i` (p. 114). -/
def SimpleRecourseInstance.qsum (inst : SimpleRecourseInstance n1 m1 m2) (i : Fin m2) : ℝ :=
  inst.qplus i + inst.qminus i

/-- `K1 = {x | Ax = b, x ≥ 0}` (p. 105), as in the general instance. -/
def SimpleRecourseInstance.K1 (inst : SimpleRecourseInstance n1 m1 m2) : Set (Fin n1 → ℝ) :=
  {x | Matrix.mulVec inst.A x = inst.b ∧ ∀ j, 0 ≤ x j}

end StochasticProg.Recourse
