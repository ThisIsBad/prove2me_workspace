import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.LowerBound

open MeasureTheory ProbabilityTheory

/-- `Sj n X j` is `S_n^j = Σ_{i ≠ j} X_i = S_n − X_j` (Nagaev 1979, §1, p. 758). -/
def Sj {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ) (j : Fin n) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, X i ω

/-- `Pj P X x j` is `P_j = P(S_n ≥ x, X_j ≥ x, max_{i≠j} X_i < x)` of (1.57) (Nagaev 1979, p. 758).
The condition `max_{i≠j} X_i < x` is written `∀ i, i ≠ j → X i ω < x`, which for `n = 1` (no `i ≠ j`)
is the whole space. -/
noncomputable def Pj {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (X : Fin n → Ω → ℝ) (x : ℝ) (j : Fin n) : ℝ :=
  P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω ∧ x ≤ X j ω ∧ ∀ i, i ≠ j → X i ω < x}

end NagaevLD.LowerBound
