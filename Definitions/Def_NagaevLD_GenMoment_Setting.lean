import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.GenMoment

open MeasureTheory

/-- The generalized moment `b_gj = E[e^{g(X_j)}; X_j ≥ 0]` (p. 759), taken over the event
`X_j ≥ 0` (the reading the proof of Theorem 2.5 uses, see (2.46)). -/
noncomputable def bg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (g : ℝ → ℝ) (j : Fin n) : ℝ :=
  ∫ ω in {ω | 0 ≤ X j ω}, Real.exp (g (X j ω)) ∂P

/-- `b_j(s) = e^{g(0)} E[e^{g'(s) X_j}; X_j < 0]` (Theorem 2.5, p. 767), where `g'` is the
derivative of `g`. -/
noncomputable def bj {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (g g' : ℝ → ℝ) (j : Fin n) (s : ℝ) : ℝ :=
  Real.exp (g 0) * ∫ ω in {ω | X j ω < 0}, Real.exp (g' s * X j ω) ∂P

end NagaevLD.GenMoment
