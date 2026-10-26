import Mathlib

namespace AdaptDRO.LiftedLDR

/-- A free-variable linear recourse problem with constraints `B y ≥ t`. -/
structure RecourseLP (M N : ℕ) where
  B : Matrix (Fin M) (Fin N) ℝ
  d : Fin N → ℝ

def RecourseLP.Feasible {M N : ℕ} (R : RecourseLP M N) (t : Fin M → ℝ) : Prop :=
  ∃ y : Fin N → ℝ, t ≤ R.B.mulVec y

/-- The real LP minimum; its use requires primal and dual feasibility. -/
noncomputable def RecourseLP.value {M N : ℕ} (R : RecourseLP M N)
    (t : Fin M → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ y : Fin N → ℝ, t ≤ R.B.mulVec y ∧ c = dotProduct R.d y}

def RecourseLP.Complete {M N : ℕ} (R : RecourseLP M N) : Prop :=
  ∀ t : Fin M → ℝ, R.Feasible t

def RecourseLP.DualFeasible {M N : ℕ} (R : RecourseLP M N) : Prop :=
  ∃ p : Fin M → ℝ, 0 ≤ p ∧ R.B.transpose.mulVec p = R.d

end AdaptDRO.LiftedLDR
